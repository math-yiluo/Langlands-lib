import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Weyl sums and fixed vectors in the root span -/

noncomputable section

universe u₁ u₂ u₃ u₄

open scoped BigOperators

namespace Langlands.LinearAlgebra

variable {ι : Type u₁} {R : Type u₂} {M : Type u₃} {N : Type u₄}
  [Fintype ι] [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic]

omit [Fintype ι] [P.IsCrystallographic] in
/-- A reflection-fixed vector pairs trivially with every coroot. -/
theorem coroot_eq_zero_of_reflection_fixed {x : M}
    (hfixed : ∀ i, P.reflection i x = x) (i : ι) : P.coroot' i x = 0 := by
  have hz : (P.coroot' i x) • P.root i = 0 := by
    exact sub_eq_self.mp ((P.reflection_apply i x).symm.trans (hfixed i))
  exact (smul_eq_zero.mp hz).resolve_right (P.ne_zero i)

/-- The root span contains no nonzero vector fixed by every root reflection. -/
theorem eq_zero_of_mem_rootSpan_of_reflection_fixed {x : M}
    (hx : x ∈ P.rootSpan R) (hfixed : ∀ i, P.reflection i x = x) : x = 0 := by
  have hker : x ∈ LinearMap.ker P.RootForm := by
    rw [LinearMap.mem_ker]
    ext y
    simp [P.rootForm_apply_apply, coroot_eq_zero_of_reflection_fixed P hfixed]
  have hmem : x ∈ P.rootSpan R ⊓ LinearMap.ker P.RootForm := ⟨hx, hker⟩
  simpa only [P.disjoint_rootSpan_ker_rootForm.eq_bot, Submodule.mem_bot] using hmem

/-- The root span contains no nonzero Weyl-fixed vector. -/
theorem eq_zero_of_mem_rootSpan_of_weyl_fixed {x : M}
    (hx : x ∈ P.rootSpan R) (hfixed : ∀ w : P.weylGroup, w • x = x) : x = 0 := by
  apply eq_zero_of_mem_rootSpan_of_reflection_fixed P hx
  intro i
  exact hfixed (RootPairing.weylGroup.ofIdx P i)

omit [Fintype ι] [CharZero R] [P.IsCrystallographic] in
/-- The Weyl action preserves the span of roots. -/
theorem weyl_smul_mem_rootSpan (w : P.weylGroup) {x : M} (hx : x ∈ P.rootSpan R) :
    w • x ∈ P.rootSpan R := by
  have hle : P.rootSpan R ≤ (P.rootSpan R).comap (P.weylGroupRootRep w) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change w • P.root i ∈ P.rootSpan R
    rw [P.weylGroup_apply_root]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact hle hx

section FiniteWeylGroup

variable [Fintype P.weylGroup]

/-- The unnormalized sum of the natural Weyl representation on the weight space. -/
def weylSum : M →ₗ[R] M := ∑ w : P.weylGroup, P.weylGroupRootRep w

omit [Fintype ι] [CharZero R] [P.IsCrystallographic] in
@[simp]
theorem weylSum_apply (x : M) : weylSum P x = ∑ w : P.weylGroup, w • x := by
  simp [weylSum, RootPairing.weylGroupRootRep]

omit [Fintype ι] [CharZero R] [P.IsCrystallographic] in
/-- The Weyl sum is Weyl-fixed. -/
theorem weylSum_fixed (x : M) (w : P.weylGroup) : w • weylSum P x = weylSum P x := by
  rw [weylSum_apply, Finset.smul_sum]
  simp_rw [← mul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun _ => rfl)

/-- The Weyl sum annihilates the entire span of roots. -/
theorem weylSum_eq_zero_of_mem_rootSpan {x : M} (hx : x ∈ P.rootSpan R) :
    weylSum P x = 0 := by
  apply eq_zero_of_mem_rootSpan_of_weyl_fixed P
  · rw [weylSum_apply]
    exact Submodule.sum_mem _ fun w _ => weyl_smul_mem_rootSpan P w hx
  · exact weylSum_fixed P x

end FiniteWeylGroup

end Langlands.LinearAlgebra
