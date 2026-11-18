import Langlands.BushnellKutzko.NormalizedLevel
import Langlands.HarmonicAnalysis.Conductor

/-! # Normalized level of a twist by `χ ∘ det` (statement L2)

Operator route note, Lemma `lem:level`(ii): an internal result of the note, proved there from
statement L1. -/

noncomputable section

namespace Langlands.BushnellKutzko

section Instances

/-! The canonical instances have module-specific names, so that the sibling statement modules
of this namespace can be imported together. -/

local instance levelTwistTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance levelTwistTopologicalSpaceGL {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **L2.** Let `K : PadicField p`, `n ≥ 1`, `χ` a quasicharacter of `K^×` with Swan exponent
`k = a(χ) - 1` (truncated; `a(χ)` is `multiplicativeConductor χ`), and `a` a class of
irreducible admissible complex representations of `GL_n(K)`. If `x` is the normalized level of
`a` and `y` that of its twist by `χ ∘ det`, then `y ≤ max x k`, with equality when `x ≠ k`. -/
def NormalizedLevelTwistStatement.{uK, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ), 1 ≤ n →
    ∀ (χ : HarmonicAnalysis.Quasicharacter K.Carrier) (k : ℕ),
      k = K.canonicalTopologicalData.multiplicativeConductor χ - 1 →
    ∀ (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)) (x y : ℚ),
      IsNormalizedLevel K n a x →
      IsNormalizedLevel K n
        (SmoothDualClass.twist (χ.toMonoidHom.comp (GeneralLinear.determinant (n := n)))
          (isOpen_ker_determinantCharacter K n χ) a) y →
      y ≤ max x (k : ℚ) ∧ (x ≠ (k : ℚ) → y = max x (k : ℚ))

end Instances

end Langlands.BushnellKutzko
