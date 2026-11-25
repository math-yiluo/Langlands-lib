/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization

/-! # The unit equation for the mate of pullback composition

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-mate-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback schemeHomPullbackAdjunction
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Adjunction.comp DerivedCategory.Qh
private theorem mate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {K : D} (β : M ⟶ R₁.obj K) (γ : M ⟶ R₂.obj K)
    (h : α.app M ≫ L₁.map β ≫ a₁.counit.app K =
      L₂.map γ ≫ a₂.counit.app K) :
    β ≫ (conjugateEquiv a₁ a₂ α).app K = γ := by
  apply (a₂.homEquiv M K).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← Category.assoc, α.naturality, Category.assoc]
  exact h

private theorem mate_transpose_to
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {K : D} (β : M ⟶ R₁.obj K) (δ : L₂.obj M ⟶ K)
    (h : α.app M ≫ L₁.map β ≫ a₁.counit.app K = δ) :
    β ≫ (conjugateEquiv a₁ a₂ α).app K = a₂.homEquiv M K δ := by
  apply mate_transpose a₁ a₂ α
  have hδ : L₂.map ((a₂.homEquiv M K) δ) ≫ a₂.counit.app K = δ := by
    simpa only [Adjunction.homEquiv_symm_apply] using
      (a₂.homEquiv M K).symm_apply_apply δ
  exact h.trans hδ.symm

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

set_option linter.all false in
-- Avoid repeating the expensive chosen-object type comparisons during linting.
-- Matching the composition expands the sheaf and derived-functor instances.
/-- The conjugate of the fixed pullback comparison satisfies the pasted direct-image
unit equation, before identifying it with any direct-image composition isomorphism.
Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-mate-unit).

Proof: compute the two transposes under the composite pinned adjunction. The
chosen-comparison counit normalization identifies the transpose of the composite
unit followed by the mate with the explicit pasted underived counits. The proved
pasted-unit counit normalization computes the other transpose as the same expression.
Transitivity identifies them. Injectivity of the composite Hom equivalence and
Mathlib conjugateEquiv_counit, together with naturality of the pullback comparison,
give the displayed equation. No resolution, exactness or cancellation hypothesis is
used in this formal combination. The remaining comparison calculation is the named
statement derivedPullbackComposition_counit_normalization. Identity morphisms,
zero complexes and empty schemes use the same equations. -/
theorem derivedPullbackComposition_mate_unit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let p : ∀ {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C),
        derivedPullback t ⋙ derivedPullback s ≅ derivedPullback (s ≫ t) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
        (conjugateEquiv (schemeHomPullbackAdjunction.{u, w} (f ≫ g))
          ((schemeHomPullbackAdjunction.{u, w} g).comp (schemeHomPullbackAdjunction.{u, w} f))
          (p f g).hom).app (DerivedCategory.Qh.obj K) =
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (schemeDerivedDirectImage g).map
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K)
    := by
  classical
  intro p
  exact (mate_transpose_to (schemeHomPullbackAdjunction.{u, w} (f ≫ g))
    ((schemeHomPullbackAdjunction.{u, w} g).comp
      (schemeHomPullbackAdjunction.{u, w} f)) (p f g).hom
    ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K)
    (derivedCompositionCounitApex f g K)
    (derivedPullbackComposition_counit_normalization.{u, w} f g K)).trans
      (derivedDirectImage_pasted_counit_normalization.{u, w} f g K)

end AlgebraicGeometry
