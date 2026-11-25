/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Algebra.Homology.Monoidal.Supertrace
public import WeilConjectures.CategoryTheory.Shift.ShiftDecomposition

/-!
# Traces along decompositions into shifts

For a decomposition `P ≅ ⨁ⱼ E⟦nⱼ⟧` (`CategoryTheory.ShiftDecomposition`), the categorical trace
of an endomorphism `v` of `P` is the sum of the traces of its diagonal blocks
`E⟦nⱼ⟧ ⟶ P ⟶ P ⟶ E⟦nⱼ⟧` (`CategoryTheory.ShiftDecomposition.trace_eq_sum`), and likewise for
the trace of the linear map induced by an additive functor to modules over a field
(`CategoryTheory.ShiftDecomposition.linearMapTrace_eq_sum`). Both follow from the cyclicity of
the trace and `∑ⱼ pⱼ ≫ iⱼ = 𝟙`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.ShiftDecomposition

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ] {E P : C}
  (D : ShiftDecomposition E P)

section Monoidal

variable [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]

/-- The categorical trace of an endomorphism of `⨁ⱼ E⟦nⱼ⟧` is the sum of the traces of its
diagonal blocks. -/
theorem trace_eq_sum [HasRightDual P] [∀ n : ℤ, HasRightDual ((shiftFunctor C n).obj E)]
    (v : P ⟶ P) : trace v = ∑ j, trace (D.incl j ≫ v ≫ D.proj j) := by
  calc trace v = trace ((∑ j, D.proj j ≫ D.incl j) ≫ v) := by rw [D.total, Category.id_comp]
    _ = ∑ j, trace (D.proj j ≫ D.incl j ≫ v) := by
        rw [Preadditive.sum_comp, ← traceAddMonoidHom_apply, map_sum]
        simp only [traceAddMonoidHom_apply, Category.assoc]
    _ = ∑ j, trace (D.incl j ≫ v ≫ D.proj j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [trace_comp_comm, Category.assoc]

end Monoidal

section Linear

variable {K : Type*} [Field K] (F : C ⥤ ModuleCat K) [F.Additive]

/-- The trace of the linear map induced by an endomorphism of `⨁ⱼ E⟦nⱼ⟧` under an additive
functor to finite-dimensional vector spaces is the sum of the traces on the summands. -/
theorem linearMapTrace_eq_sum [FiniteDimensional K (F.obj P)]
    [∀ n : ℤ, FiniteDimensional K (F.obj ((shiftFunctor C n).obj E))] (v : P ⟶ P) :
    LinearMap.trace K _ (F.map v).hom =
      ∑ j, LinearMap.trace K _ (F.map (D.incl j ≫ v ≫ D.proj j)).hom := by
  calc LinearMap.trace K _ (F.map v).hom =
        LinearMap.trace K _ (F.map ((∑ j, D.proj j ≫ D.incl j) ≫ v)).hom := by
        rw [D.total, Category.id_comp]
    _ = ∑ j, LinearMap.trace K _ (F.map (D.proj j ≫ D.incl j ≫ v)).hom := by
        rw [Preadditive.sum_comp, F.map_sum, ModuleCat.hom_sum, map_sum]
        simp only [Category.assoc]
    _ = ∑ j, LinearMap.trace K _ (F.map (D.incl j ≫ v ≫ D.proj j)).hom := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [F.map_comp, ModuleCat.hom_comp, LinearMap.trace_comp_comm', ← ModuleCat.hom_comp,
          ← F.map_comp, Category.assoc]

/-- An element of `F(⨁ⱼ E⟦nⱼ⟧)` is the sum of its components. -/
lemma sum_map_incl_map_proj (z : F.obj P) :
    ∑ j, (F.map (D.incl j)).hom ((F.map (D.proj j)).hom z) = z := by
  have h := congrArg (fun φ ↦ (F.map φ).hom z) D.total
  simp only [F.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, F.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, F.map_id, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  exact h

include D in
/-- An additive functor to vector spaces takes finite-dimensional values on `⨁ⱼ E⟦nⱼ⟧` if it does
on the shifts of `E`. -/
lemma finiteDimensional_obj [∀ n : ℤ, FiniteDimensional K (F.obj ((shiftFunctor C n).obj E))] :
    FiniteDimensional K (F.obj P) :=
  Module.Finite.of_injective (LinearMap.pi fun j ↦ (F.map (D.proj j)).hom) fun x y h ↦ by
    rw [← D.sum_map_incl_map_proj F x, ← D.sum_map_incl_map_proj F y]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [show (F.map (D.proj j)).hom x = (F.map (D.proj j)).hom y from congrFun h j]

include D in
/-- An additive functor to vector spaces vanishes on `⨁ⱼ E⟦nⱼ⟧` if it vanishes on the summands. -/
lemma subsingleton_obj (h : ∀ j, Subsingleton (F.obj ((shiftFunctor C (D.deg j)).obj E))) :
    Subsingleton (F.obj P) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [← D.sum_map_incl_map_proj F x, ← D.sum_map_incl_map_proj F y]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [Subsingleton.elim ((F.map (D.proj j)).hom x) ((F.map (D.proj j)).hom y)]

end Linear

end CategoryTheory.ShiftDecomposition
