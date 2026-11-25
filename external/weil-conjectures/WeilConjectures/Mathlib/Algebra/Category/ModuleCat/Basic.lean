/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite modules over an infinite field, and the dual functor

## Main definitions

- `ModuleCat.dualFunctor`: the contravariant functor `V ↦ Module.Dual R V` on `R`-modules.
- `ModuleCat.dualDualIso`: the double dual of a functor with finite-dimensional values is
  naturally isomorphic to the functor.

## Main results

- `ModuleCat.isZero_ulift_of_finite`: a finite module over (a universe lift of) an infinite
  field is zero.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

/-- A finite module over (a universe lift of) an infinite field is zero: a nonzero vector `v`
would give an injection `c ↦ c • v` of the field into the module. The ring structure on
`ULift K` is `ULift.ring`, the one appearing in `ModuleCat (ULift K)`, which is not reducibly
the one underlying `ULift.field`. -/
theorem ModuleCat.isZero_ulift_of_finite {K : Type v} [Field K] [Infinite K]
    (M : ModuleCat.{w} (ULift.{u} K)) [Finite M] : IsZero M := by
  have : Subsingleton M := by
    refine subsingleton_of_forall_eq 0 fun v ↦ by_contra fun hv ↦ ?_
    refine not_finite_iff_infinite.2 inferInstance
      (Finite.of_injective (fun c : ULift.{u} K ↦ c • v) fun c d (h : c • v = d • v) ↦ ?_)
    refine by_contra fun hcd ↦ hv ?_
    rw [← one_smul (ULift.{u} K) v, ← inv_mul_cancel₀ (sub_ne_zero.2 hcd), mul_smul,
      sub_smul, h, sub_self, smul_zero]
  exact ModuleCat.isZero_of_subsingleton M


/-- The dual `V ↦ V^∨ = Module.Dual R V` as a contravariant functor on `R`-modules, sending a
linear map to its transpose. -/
@[simps]
noncomputable def ModuleCat.dualFunctor (R : Type u) [CommRing R] :
    (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{max u v} R where
  obj V := ModuleCat.of R (Module.Dual R V.unop)
  map f := ModuleCat.ofHom (Module.Dual.transpose f.unop.hom)

/-- The double dual `j ↦ K(j)^∨∨` of a functor `K` to vector spaces with finite-dimensional
values is naturally isomorphic to `K`, by the inverse of the evaluation maps
`Module.evalEquiv`. -/
noncomputable def ModuleCat.dualDualIso {C : Type*} [Category C] {k : Type u} [Field k]
    (K : Cᵒᵖ ⥤ ModuleCat.{u} k) [∀ j, FiniteDimensional k (K.obj j)] :
    (opOp C ⋙ K.op ⋙ ModuleCat.dualFunctor k).op ⋙ ModuleCat.dualFunctor k ≅ K :=
  NatIso.ofComponents (fun j ↦ (Module.evalEquiv k (K.obj j)).symm.toModuleIso) fun {i j} f ↦ by
    ext x
    apply (Module.evalEquiv k (K.obj j)).injective
    ext ψ
    change ψ ((Module.evalEquiv k (K.obj j)).symm
        (Module.Dual.transpose (Module.Dual.transpose (K.map f).hom) x)) =
      ψ ((K.map f).hom ((Module.evalEquiv k (K.obj i)).symm x))
    rw [Module.apply_evalEquiv_symm_apply, ← LinearMap.comp_apply ψ (K.map f).hom]
    exact (Module.apply_evalEquiv_symm_apply (f := ψ ∘ₗ (K.map f).hom) (g := x)).symm

/-- Composing a linear map with isomorphisms on both sides does not change the dimension of its
range: `dim range (a ≫ m ≫ b) = dim range m` for isomorphisms `a` and `b`. -/
lemma ModuleCat.finrank_range_iso_comp {R : Type*} [Ring R] {M N M' N' : ModuleCat.{u} R}
    (a : M' ≅ M) (m : M ⟶ N) (b : N ≅ N') :
    Module.finrank R (LinearMap.range (a.hom ≫ m ≫ b.hom).hom) =
      Module.finrank R (LinearMap.range m.hom) := by
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 (ConcreteCategory.bijective_of_isIso a.hom).2, Submodule.map_top,
    LinearMap.range_comp]
  exact b.toLinearEquiv.finrank_map_eq _
