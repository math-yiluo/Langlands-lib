import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction

/-! # Inducing data for the real generic unitary dual -/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- A unitary square-integrable-modulo-center block, with the positive weight convention
for the `GL₂(ℝ)` discrete series. -/
def IsRealUnitaryDiscreteBlock (δ : RealBlock) : Prop :=
  realBlockExponent δ = 0 ∧
    match δ with
    | .character _ => True
    | .induced d => 0 < d.weight

/-- The ordered block list of a basis element in the generic unitary dual: a unitary
square-integrable block or a complementary pair of real determinant twists. -/
def IsRealGenericUnitaryInducingFactor (ds : List RealBlock) : Prop :=
  ∃ δ : RealBlock, IsRealUnitaryDiscreteBlock δ ∧
    (ds = [δ] ∨ ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧
      ds = [realBlockTwist α δ, realBlockTwist (-α) δ])

/-- A concatenation of inducing block lists of generic unitary basis elements. -/
def IsRealGenericUnitaryInducingData (ds : List RealBlock) : Prop :=
  ∃ factors : List (List RealBlock), factors.flatten = ds ∧
    ∀ factor ∈ factors, IsRealGenericUnitaryInducingFactor factor

/-- Every block in the inducing data of a generic unitary product has real exponent in
`(-1/2, 1/2)`. -/
theorem IsRealGenericUnitaryInducingData.exponent_bound {ds : List RealBlock}
    (h : IsRealGenericUnitaryInducingData ds) {x : RealBlock} (hx : x ∈ ds) :
    |realBlockExponent x| < 1 / 2 := by
  obtain ⟨factors, rfl, hfactors⟩ := h
  obtain ⟨factor, hfactor, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨δ, hδ, hsingle | ⟨α, hα, hα', hpair⟩⟩ := hfactors factor hfactor
  · subst factor
    obtain rfl := List.mem_singleton.mp hx
    rw [hδ.1, abs_zero]
    norm_num
  · subst factor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rwa [realBlockExponent_twist, hδ.1, zero_add, abs_of_pos hα]
    · rwa [realBlockExponent_twist, hδ.1, zero_add, abs_neg, abs_of_pos hα]

end Langlands.Archimedean
