import Langlands.Algebra.NilpotentModuleReduction
import Langlands.Algebra.NilpotentModuleFiniteness
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Convolution duals through nilpotent scalar reduction -/

noncomputable section

universe u v

open Coalgebra WithConv TensorProduct Module

namespace Langlands.CoalgebraNilpotentReduction

variable {R : Type u} [CommRing R]
  {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Reduction of the values of convolution functionals modulo a base ideal. -/
def reduction (I : Ideal R) :
    WithConv (C →ₗ[R] R) →ₐ[R] WithConv (C →ₗ[R] R ⧸ I) where
  toFun f := toConv ((Ideal.Quotient.mkₐ R I).toLinearMap.comp f.ofConv)
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by
    ext x
    simp
  map_mul' f g := by
    apply WithConv.ext
    exact LinearMap.algHom_comp_convMul_distrib (Ideal.Quotient.mkₐ R I) f g
  commutes' r := by
    ext x
    simp [Algebra.smul_def]

@[simp]
theorem reduction_apply (I : Ideal R) (f : WithConv (C →ₗ[R] R)) (x : C) :
    reduction I f x = Ideal.Quotient.mk I (f x) := rfl

/-- Projectivity supplies all lifts of reduced functionals. -/
theorem reduction_surjective [Module.Projective R C] (I : Ideal R) :
    Function.Surjective (reduction (C := C) I) := by
  intro f
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (Ideal.Quotient.mkₐ R I).toLinearMap f.ofConv Ideal.Quotient.mk_surjective
  exact ⟨toConv g, WithConv.ext hg⟩

/-- A convolution power of a functional valued in `I` takes values in `I^n`. -/
theorem pow_apply_mem (I : Ideal R) (f : WithConv (C →ₗ[R] R))
    (hf : ∀ x, f x ∈ I) (n : ℕ) (x : C) : (f ^ n) x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ f n, (Repr.arbitrary R x).convMul_apply]
    apply Submodule.sum_mem
    intro j hj
    rw [pow_succ]
    exact Ideal.mul_mem_mul (ih _) (hf _)

/-- The kernel of convolution reduction consists of nilpotent elements. -/
theorem isNilpotent_of_reduction_eq_zero (I : Ideal R) (hI : IsNilpotent I)
    (f : WithConv (C →ₗ[R] R)) (hf : reduction I f = 0) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  ext x
  have hfx (y : C) : f y ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrArg (fun g : WithConv (C →ₗ[R] R ⧸ I) => g y) hf
  have h := pow_apply_mem I f hfx n x
  simpa only [hn, Ideal.zero_eq_bot, Ideal.mem_bot,
    WithConv.ofConv_zero, LinearMap.zero_apply] using h

/-- A finite complete orthogonal family in the reduced convolution dual lifts. -/
theorem exists_lift_completeOrthogonalIdempotents
    [Module.Projective R C] (I : Ideal R) (hI : IsNilpotent I)
    {ι : Type v} [Fintype ι] (e : ι → WithConv (C →ₗ[R] R ⧸ I))
    (he : CompleteOrthogonalIdempotents e) :
    ∃ e' : ι → WithConv (C →ₗ[R] R),
      CompleteOrthogonalIdempotents e' ∧ ∀ j, reduction I (e' j) = e j := by
  obtain ⟨e', he', hmap⟩ := he.lift_of_isNilpotent_ker
    (reduction (C := C) I).toRingHom
    (fun f hf => isNilpotent_of_reduction_eq_zero I hI f hf)
    (fun j => (reduction_surjective I (e j)))
  exact ⟨e', he', fun j => congrFun hmap j⟩

/-- In a finite free coalgebra, scalar reduction has exactly the expected
module-theoretic kernel. -/
theorem ker_reduction [Module.Free R C] [Module.Finite R C] (I : Ideal R) :
    LinearMap.ker (reduction (C := C) I).toLinearMap =
      I • (⊤ : Submodule R (WithConv (C →ₗ[R] R))) := by
  classical
  apply le_antisymm
  · intro f hf
    let b := Module.Free.chooseBasis R C
    let d := b.dualBasis.map (WithConv.linearEquiv R (C →ₗ[R] R)).symm
    rw [← d.sum_repr f]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem_smul _ (Submodule.mem_top)
    change b.dualBasis.repr f.ofConv j ∈ I
    rw [Basis.dualBasis_repr]
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (congrArg (fun g : WithConv (C →ₗ[R] R ⧸ I) => g (b j)) hf)
  · refine Submodule.smul_le.mpr ?_
    intro r hr f hf
    change reduction I (r • f) = 0
    ext x
    change Ideal.Quotient.mk I (r * f x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right (f x) hr)

/-- Any family whose scalar reductions span already spans the convolution dual. -/
theorem span_eq_top_of_reduction [Module.Free R C] [Module.Finite R C]
    (I : Ideal R) (hI : IsNilpotent I)
    {ι : Type*} (e : ι → WithConv (C →ₗ[R] R))
    (he : Submodule.span R (Set.range (fun j => reduction I (e j))) = ⊤) :
    Submodule.span R (Set.range e) = ⊤ := by
  apply Langlands.Algebra.eq_top_of_sup_smul_eq_top_of_nilpotent I hI
  rw [← ker_reduction I]
  apply (LinearMap.map_eq_top_iff
    (LinearMap.range_eq_top.mpr (reduction_surjective I))).mp
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    AlgHom.toLinearMap_apply] using he

/-- Complete orthogonal idempotents spanning the reduced dual lift to a spanning
complete orthogonal family in the original convolution dual. -/
theorem exists_lift_spanning_completeOrthogonalIdempotents
    [Module.Free R C] [Module.Finite R C] (I : Ideal R) (hI : IsNilpotent I)
    {ι : Type v} [Fintype ι] (e : ι → WithConv (C →ₗ[R] R ⧸ I))
    (he : CompleteOrthogonalIdempotents e)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    ∃ e' : ι → WithConv (C →ₗ[R] R),
      CompleteOrthogonalIdempotents e' ∧
      (∀ j, reduction I (e' j) = e j) ∧
      Submodule.span R (Set.range e') = ⊤ := by
  obtain ⟨e', he', hmap⟩ := exists_lift_completeOrthogonalIdempotents I hI e he
  refine ⟨e', he', hmap, span_eq_top_of_reduction I hI e' ?_⟩
  simpa only [hmap] using hspan

end Langlands.CoalgebraNilpotentReduction
