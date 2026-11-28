import Langlands.LinearAlgebra.GMFamilyCentralSubspaceDescent
import Langlands.LinearAlgebra.GMFamilySliceSpecial

/-! # Descent of `(G, M)`-families to a special subspace -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Submodule

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a a₁ : Submodule ℝ E} {ξ : E}

/-- For a special coarse subspace, the fine vertex sums over the coarse chambers take the values
required by the descent formula. -/
theorem hasLiftVertexSums_of_special (D : CentralSubspaceDescent.DescentPosition R a a₁ ξ) {m : E → ℝ}
    (hm : IsSpecialSubspace R a a₁ m) (Λ : StrongDual ℝ a)
    (hΛ : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0) :
    CentralSubspaceDescent.HasLiftVertexSums R a a₁ ξ Λ :=
  fun _ _ hS hP hSP => SpecialSlice.vertexSum_eq_of_special_extension D hm hS hP hSP Λ hΛ

/-- **Arthur's descent to a special subspace.** For a root set `R`, a Levi flat `a₁`, a subspace
`a ⊆ a₁` containing the central space which is special for positive weights `m`, a
`(G, M₁)`-family on `a₁` and a displacement `ξ ∈ a₁ ∩ aᗮ` in general position, the supplementary
function of the induced family on `a` is the sum over the Levi flats of `a₁` of the descent
coefficients times the relative supplementary functions at the selected sections, at every
parameter on which no nonzero restriction of a root to `a` vanishes. -/
theorem specialDescentFormula (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (haa₁ : a ≤ a₁)
    (hz : centralSpace R ≤ a) {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) (hc₁ : IsFamily R a₁ c₁)
    (hξ : ξ ∈ a₁ ⊓ aᗮ)
    (hgen : ∀ L ∈ leviSpaces R a₁, dDescent a (centralSpace R) a₁ L ≠ 0 →
      ∀ p, p ∈ noncentral R L → p - ξ ∈ noncentral R a → IsRegular R L p)
    (Λ : StrongDual ℝ a) (hΛ : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0) :
    cM R a (inducedFamily R a a₁ c₁) Λ =
      ∑ L ∈ leviSpaces R a₁, (dDescent a (centralSpace R) a₁ L : ℂ) *
        cQM R a₁ c₁ (descentSection R a (centralSpace R) ξ L) (extendParam a a₁ Λ) := by
  let D : CentralSubspaceDescent.DescentPosition R a a₁ ξ := ⟨hR, hz, ha₁, haa₁, hξ, hgen⟩
  exact CentralSubspaceDescent.cM_induced_eq_descentSum D c₁ hc₁ Λ hΛ (hasLiftVertexSums_of_special D hm Λ hΛ)

end Langlands.GMFamily
