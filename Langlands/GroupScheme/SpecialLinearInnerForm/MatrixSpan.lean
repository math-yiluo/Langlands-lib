import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Matrix.Basis

/-! # Special linear matrices span the full matrix algebra -/

noncomputable section

namespace Langlands.GroupScheme.SpecialLinearInnerForm

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Over every commutative ring, the special linear matrices span the matrix algebra
as a module. This includes empty and singleton index types. -/
theorem span_specialLinear :
    Submodule.span R (Set.range (fun g : Matrix.SpecialLinearGroup ι R =>
      (g : Matrix ι ι R))) = ⊤ := by
  let P := Submodule.span R (Set.range (fun g : Matrix.SpecialLinearGroup ι R =>
    (g : Matrix ι ι R)))
  have hmem (g : Matrix.SpecialLinearGroup ι R) : (g : Matrix ι ι R) ∈ P :=
    Submodule.subset_span ⟨g, rfl⟩
  have h1 : (1 : Matrix ι ι R) ∈ P := hmem 1
  have hoff (i j : ι) (hij : i ≠ j) : single i j (1 : R) ∈ P := by
    have h := P.sub_mem (hmem (Matrix.SpecialLinearGroup.transvection hij 1)) h1
    simpa only [Matrix.SpecialLinearGroup.transvection_coe, add_sub_cancel_left] using h
  have hdiag (i : ι) : single i i (1 : R) ∈ P := by
    rcases subsingleton_or_nontrivial ι with hι | hι
    · have he : single i i (1 : R) = (1 : Matrix ι ι R) := by
        ext a b
        have ha : a = i := Subsingleton.elim a i
        have hb : b = i := Subsingleton.elim b i
        subst a
        subst b
        simp
      rw [he]
      exact h1
    · obtain ⟨j, hji⟩ := exists_ne i
      let t := Matrix.SpecialLinearGroup.transvection hji.symm (1 : R)
      let s := Matrix.SpecialLinearGroup.transvection hji (1 : R)
      have he : ((t * s : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) -
          (t : Matrix ι ι R) - (s : Matrix ι ι R) + 1 = single i i (1 : R) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul, t, s,
          Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul,
          Matrix.one_mul, single_mul_single_same, mul_one]
        abel
      rw [← he]
      exact P.add_mem (P.sub_mem (P.sub_mem (hmem (t * s)) (hmem t)) (hmem s)) h1
  have hsingle (i j : ι) (r : R) : single i j r ∈ P := by
    have h : single i j (1 : R) ∈ P := by
      by_cases hij : i = j
      · subst j
        exact hdiag i
      · exact hoff i j hij
    simpa only [smul_single, smul_eq_mul, mul_one] using P.smul_mem r h
  apply top_unique
  intro X _
  change X ∈ P
  rw [Matrix.matrix_eq_sum_single X]
  exact P.sum_mem fun i _ => P.sum_mem fun j _ => hsingle i j (X i j)

/-- Linear maps on matrices are determined by their values on special linear
matrices, in every characteristic and in every size. -/
theorem linearMap_ext_specialLinear {V : Type*} [AddCommGroup V] [Module R V]
    (f g : Matrix ι ι R →ₗ[R] V)
    (h : ∀ x : Matrix.SpecialLinearGroup ι R, f x = g x) : f = g := by
  apply LinearMap.ext
  intro X
  have hx : X ∈ Submodule.span R (Set.range (fun x : Matrix.SpecialLinearGroup ι R =>
      (x : Matrix ι ι R))) := by
    rw [span_specialLinear]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact h x
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

end Langlands.GroupScheme.SpecialLinearInnerForm
