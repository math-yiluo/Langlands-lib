/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomNormalizedShift
import Mathlib.CategoryTheory.Triangulated.Adjunction

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

private theorem opposite_shift_component
    {D E : Type*} [Category D] [Category E] [HasShift D ℤ] [HasShift E ℤ]
    [Preadditive D] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (F : D ⥤ E) [F.CommShift ℤ] (K : D) (n : ℤ) :
    letI := Pretriangulated.Opposite.commShiftFunctorOpInt F
    (F.op.commShiftIso n).hom.app (op K) = ((F.commShiftIso (-n)).inv.app K).op := by
  rw [Functor.op_commShiftIso_hom_app F (op K) n (-n) (add_neg_cancel n)]
  change (F.map (𝟙 (K⟦-n⟧))).op ≫ ((F.commShiftIso (-n)).inv.app K).op ≫
    𝟙 (op ((F.obj K)⟦-n⟧)) = _
  rw [F.map_id, op_id, Category.id_comp]
  exact Category.comp_id _

private theorem scalar_extension_exact
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u}) (φ : A →+* B) :
    letI := etaleHomScalarCommShift X φ
    (scalarExtension φ X).IsTriangulated := by
  let adj := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  letI : (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).leftAdjoint.CommShift ℤ :=
    adj.leftAdjointCommShift ℤ
  letI : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  exact adj.isTriangulated_leftAdjoint

private theorem opposite_composite_component
    {D E : Type*} [Category D] [Category E] [HasShift D ℤ] [HasShift E ℤ]
    [Preadditive D] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (F : D ⥤ E) [F.CommShift ℤ] (H : Eᵒᵖ ⥤ E) [H.CommShift ℤ]
    (K : D) (n : ℤ) :
    letI := Pretriangulated.Opposite.commShiftFunctorOpInt F
    ((F.op ⋙ H).commShiftIso n).hom.app (op K) =
      H.map (((F.commShiftIso (-n)).inv.app K).op) ≫
        (H.commShiftIso n).hom.app (op (F.obj K)) := by
  rw [Functor.commShiftIso_comp_hom_app, opposite_shift_component]
  rfl

/-- The normalized étale Hom shift data except for the left comparison equation.
Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact-shift-data`, proof steps 1--2.

The native signed exact Hom theorem and its mate evaluation identity supply
both normalized Hom shifts. Triangulated adjunction gives exactness of scalar
extension; the composite and opposite shift formulas give the right component
equation and both composite triangulated structures. The omitted left component
equation is the definitional composition formula proved in the parent module.
(blueprint: lem-coef-etale-hom-transpose-exact-shift-core) -/
theorem etaleHomComparison_reversedExact_shiftCore
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X) :
    letI := etaleHomScalarCommShift X φ
    ∃ (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
      (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
        ((scalarExtension φ X).obj M)).CommShift ℤ),
      EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA ∧
      EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X ((scalarExtension φ X).obj M) sB ∧
      (letI : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
          ((scalarExtension φ X).obj M)).CommShift ℤ := sB
       letI : (scalarExtension φ X).op.CommShift ℤ :=
         Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)
       letI : (EtaleHomRight X φ M).CommShift ℤ :=
         @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
           (Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)) sB
       ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
          ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
              ((scalarExtension φ X).obj M)).map
            ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) ∧
      (letI : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ := sA
       letI : (EtaleHomLeft X φ M).CommShift ℤ :=
         @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ sA
           (etaleHomScalarCommShift X φ)
       (EtaleHomLeft X φ M).IsTriangulated) ∧
      (letI : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
          ((scalarExtension φ X).obj M)).CommShift ℤ := sB
       letI : (scalarExtension φ X).op.CommShift ℤ :=
         Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)
       letI : (EtaleHomRight X φ M).CommShift ℤ :=
         @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
           (Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)) sB
       (EtaleHomRight X φ M).IsTriangulated) := by
  letI := etaleHomScalarCommShift X φ
  obtain ⟨sA, hA, hTriA⟩ := etaleHom_normalizedShift_exists (ModuleCat.{u + 1} A) X M
  obtain ⟨sB, hB, hTriB⟩ := etaleHom_normalizedShift_exists (ModuleCat.{u + 1} B) X
    ((scalarExtension φ X).obj M)
  letI : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ := sA
  letI : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
    ((scalarExtension φ X).obj M)).CommShift ℤ := sB
  haveI : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).IsTriangulated := hTriA
  haveI : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
    ((scalarExtension φ X).obj M)).IsTriangulated := hTriB
  haveI : (scalarExtension φ X).IsTriangulated := scalar_extension_exact X φ
  refine ⟨sA, sB, hA, hB, ?_, ?_, ?_⟩
  · intro K n
    exact opposite_composite_component (scalarExtension φ X)
      ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj ((scalarExtension φ X).obj M)) K n
  · exact inferInstanceAs (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M ⋙
      scalarExtension φ X).IsTriangulated)
  · letI : (scalarExtension φ X).op.CommShift ℤ :=
      Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)
    exact inferInstanceAs (((scalarExtension φ X).op ⋙
      (derivedHom (ModuleCat.{u + 1} B) X).flip.obj
        ((scalarExtension φ X).obj M)).IsTriangulated)

end AlgebraicGeometry.Etale
