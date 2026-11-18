import Langlands.BushnellKutzko.NormalizedLevel
import Langlands.Correspondence.HenniartNumericalStatement

/-! # Swan conductor of a supercuspidal equals rank times normalized level (statement T2)

Operator route note, Proposition `prop:T2` and Lemma `lem:level`(i), second sentence;
Bushnell (1987), Theorem 3, printed p. 198; Bushnell–Fröhlich (1985), (3.3.8), printed p. 258. -/

noncomputable section

namespace Langlands.BushnellKutzko

section Instances

/-! The canonical instances have module-specific names, so that the sibling statement modules
of this namespace can be imported together. -/

local instance swanLevelTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance swanLevelTopologicalSpaceGL {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **T2.** For every `K : PadicField p`, every `k : ℕ` and every supercuspidal class `π` of
`GL_{k+1}(K)` with normalized level `x`, the conductor `Numerical.conductor K π` is a natural
number `c`, and `c - (k + 1) = (k + 1) x` (truncated subtraction): `sw(π) = n · ℓ(π)` with
`n = k + 1`. -/
def SupercuspidalSwanLevelStatement.{uK, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) (x : ℚ),
    IsNormalizedLevel K (k + 1) (Correspondence.supercuspidalToAutomorphic K π) x →
    ∃ c : ℕ, Henniart.Numerical.conductor K π = (c : WithTop ℕ) ∧
      ((c - (k + 1) : ℕ) : ℚ) = ((k + 1 : ℕ) : ℚ) * x

end Instances

end Langlands.BushnellKutzko
