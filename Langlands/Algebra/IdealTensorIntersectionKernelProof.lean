import Langlands.Algebra.IdealTensorIntersectionKernelStatement
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Proof of the ideal intersection tensor-kernel transport -/

universe u v

namespace Langlands.Algebra

open TensorProduct LinearMap

/-- Proof of `IdealTensorIntersectionKernelStatement`: tensor the exact pair
`a ⊓ J → a × J → a ⊔ J` (anti-diagonal, then addition), use injectivity for `a ⊔ J`
to place the first-factor image of a kernel element in the kernel of the tensored
addition map, lift it along the tensored anti-diagonal, and project to `a`. -/
theorem idealTensorIntersectionKernel : IdealTensorIntersectionKernelStatement.{u, v} := by
  intro R M _ _ _ a J hinj x hx
  -- The anti-diagonal `c ↦ (c, -c)` and the addition map `(b, d) ↦ b + d`.
  let f : ↥(a ⊓ J) →ₗ[R] ↥a × ↥J :=
    (Submodule.inclusion inf_le_left).prod (-Submodule.inclusion inf_le_right)
  let g : ↥a × ↥J →ₗ[R] ↥(a ⊔ J) :=
    (Submodule.inclusion le_sup_left).coprod (Submodule.inclusion le_sup_right)
  have hfg : Function.Exact f g := by
    refine exact_of_comp_of_mem_range ?_ ?_
    · ext c
      simp [f, g]
    · rintro ⟨b, d⟩ hbd
      have hsum : (b : R) + d = 0 := by
        simpa [g] using congrArg Subtype.val hbd
      have hdb : (d : R) = -b := eq_neg_of_add_eq_zero_right hsum
      refine ⟨⟨b, b.2, ?_⟩, ?_⟩
      · rw [← neg_neg (b : R), ← hdb]
        exact J.neg_mem d.2
      · ext
        · rfl
        · simp [f, hdb]
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(⟨b, hb⟩, ⟨d, hd⟩), rfl⟩
  have hsub : ((a ⊔ J).subtype ∘ₗ g) ∘ₗ inl R a J = a.subtype := by
    ext; simp [g]
  have h1 : lTensor M g (lTensor M (inl R a J) x) = 0 := by
    apply hinj
    rw [map_zero, ← comp_apply, ← comp_apply, ← lTensor_comp, ← lTensor_comp, hsub]
    exact mem_ker.mp hx
  obtain ⟨z, hz⟩ := (lTensor_exact M hfg hg _).mp h1
  refine ⟨z, ?_⟩
  have hfst : fst R a J ∘ₗ f = Submodule.inclusion inf_le_left := by
    ext; simp [f]
  rw [← hfst, lTensor_comp, comp_apply, hz, ← comp_apply, ← lTensor_comp, fst_comp_inl,
    lTensor_id, id_apply]

end Langlands.Algebra
