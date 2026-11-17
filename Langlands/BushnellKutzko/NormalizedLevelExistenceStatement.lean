import Langlands.BushnellKutzko.NormalizedLevel

/-! # Existence of the normalized level (statement L0)

Bushnell (1987), (3.3), printed p. 196; operator route note, §4.4: every irreducible admissible
representation of `GL_n(K)`, `n ≥ 1`, has a normalized level `ℓ(π)`. -/

noncomputable section

namespace Langlands.BushnellKutzko

section Instances

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **L0.** For every prime `p`, every `K : PadicField p`, every `n ≥ 1` and every class `a` of
irreducible admissible complex representations of `GL_n(K)`, the set
`normalizedLevelValues K n a` has a least element: `a` has a normalized level. -/
def NormalizedLevelExistenceStatement.{uK, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ), 1 ≤ n →
    ∀ a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier),
      ∃ x : ℚ, IsNormalizedLevel K n a x

end Instances

end Langlands.BushnellKutzko
