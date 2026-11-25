/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionNormalization
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare

/-! # Counit computation for the canonical open composition comparison

Source: Stacks Project, Cohomology, Tags 08FE, 0D5T and 08BV.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

private theorem counit_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ C'} {RX : C' ⥤ C} {LY : D ⥤ D'} {RY : D' ⥤ D}
    (a : LX ⊣ RX) (b : LY ⊣ RY) (F : C ⥤ D) (G : C' ⥤ D')
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ RY)
    {A B : C'} (e : A ≅ B)
    (hA : LY.map (β.hom.app A) ≫ b.counit.app (G.obj A) =
      α.hom.app (RX.obj A) ≫ G.map (a.counit.app A)) :
    LY.map (β.hom.app B) ≫ b.counit.app (G.obj B) =
      α.hom.app (RX.obj B) ≫ G.map (a.counit.app B) := by
  let m : (RX ⋙ F) ⋙ LY ⟶ G :=
    Functor.whiskerRight β.hom LY ≫ (Functor.associator G RY LY).hom ≫
      Functor.whiskerLeft G b.counit ≫ G.rightUnitor.hom
  let n : (RX ⋙ F) ⋙ LY ⟶ G :=
    (Functor.associator RX F LY).hom ≫ Functor.whiskerLeft RX α.hom ≫
      (Functor.associator RX LX G).inv ≫ Functor.whiskerRight a.counit G ≫
      G.leftUnitor.hom
  have hi : m.app A = n.app A := by simpa [m, n] using hA
  have he : m.app B = n.app B := by
    apply (cancel_epi (((RX ⋙ F) ⋙ LY).map e.hom)).mp
    rw [m.naturality, n.naturality, hi]
  simpa [m, n] using he

-- Prove the diagram chase for abstract functors, so its rewrites do not unfold
-- the concrete restriction, homotopy, and derived-category constructions.
private theorem counit_of_unit_normalizations
    {C D A B C' D' A' B' : Type*}
    [Category C] [Category D] [Category A] [Category B]
    [Category C'] [Category D'] [Category A'] [Category B']
    {RX : A ⥤ C} {F : C ⥤ D} {G : A ⥤ B} {RY : B ⥤ D}
    {LX : C ⥤ A} {LY : D ⥤ B}
    {RX' : A' ⥤ C'} {F' : C' ⥤ D'} {G' : A' ⥤ B'} {RY' : B' ⥤ D'}
    {LX' : C' ⥤ A'} {LY' : D' ⥤ B'}
    {QX : C ⥤ C'} {QY : D ⥤ D'} {QA : A ⥤ A'} {QB : B ⥤ B'}
    (a : LX' ⊣ RX') (b : LY' ⊣ RY')
    (α : F' ⋙ LY' ≅ LX' ⋙ G') (β : RX' ⋙ F' ≅ G' ⋙ RY')
    (ηRX : RX ⋙ QX ⟶ QA ⋙ RX') (ηF : F ⋙ QY ⟶ QX ⋙ F')
    (ηG : G ⋙ QB ⟶ QA ⋙ G') (ηRY : RY ⋙ QY ⟶ QB ⋙ RY')
    (eLX : QX ⋙ LX' ≅ LX ⋙ QA) (eLY : QY ⋙ LY' ≅ LY ⋙ QB)
    (K : A)
    (α₀ : LY.obj (F.obj (RX.obj K)) ⟶ G.obj (LX.obj (RX.obj K)))
    (β₀ : F.obj (RX.obj K) ⟶ RY.obj (G.obj K))
    (εX : LX.obj (RX.obj K) ⟶ K) (εY : LY.obj (RY.obj (G.obj K)) ⟶ G.obj K)
    (ha : LX'.map (ηRX.app K) ≫ a.counit.app (QA.obj K) =
      eLX.hom.app (RX.obj K) ≫ QA.map εX)
    (hb : LY'.map (ηRY.app (G.obj K)) ≫ b.counit.app (QB.obj (G.obj K)) =
      eLY.hom.app (RY.obj (G.obj K)) ≫ QB.map εY)
    (hα : LY'.map (ηF.app (RX.obj K)) ≫ α.hom.app (QX.obj (RX.obj K)) ≫
        G'.map (eLX.hom.app (RX.obj K)) =
      eLY.hom.app (F.obj (RX.obj K)) ≫ QB.map α₀ ≫ ηG.app (LX.obj (RX.obj K)))
    (hβ : ηF.app (RX.obj K) ≫ F'.map (ηRX.app K) ≫ β.hom.app (QA.obj K) =
      QY.map β₀ ≫ ηRY.app (G.obj K) ≫ RY'.map (ηG.app K))
    (h₀ : LY.map β₀ ≫ εY = α₀ ≫ G.map εX)
    [IsIso (ηF.app (RX.obj K))] [IsIso (ηRX.app K)] :
    LY'.map (β.hom.app (QA.obj K)) ≫ b.counit.app (G'.obj (QA.obj K)) =
      α.hom.app (RX'.obj (QA.obj K)) ≫ G'.map (a.counit.app (QA.obj K)) := by
  let s := LY'.map (ηF.app (RX.obj K) ≫ F'.map (ηRX.app K))
  have : IsIso s := by dsimp [s]; infer_instance
  apply (cancel_epi s).mp
  have hl : s ≫ LY'.map (β.hom.app (QA.obj K)) ≫
      b.counit.app (G'.obj (QA.obj K)) =
    eLY.hom.app (F.obj (RX.obj K)) ≫ QB.map (LY.map β₀ ≫ εY) ≫ ηG.app K := by
    dsimp only [s]
    rw [← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [hβ]
    simp only [Functor.map_comp, Category.assoc]
    have hn : LY'.map (RY'.map (ηG.app K)) ≫ b.counit.app (G'.obj (QA.obj K)) =
      b.counit.app (QB.obj (G.obj K)) ≫ ηG.app K :=
      b.counit.naturality (ηG.app K)
    rw [hn]
    rw [← Category.assoc (LY'.map (ηRY.app (G.obj K))), hb]
    have hf : LY'.map (QY.map β₀) ≫ eLY.hom.app (RY.obj (G.obj K)) =
      eLY.hom.app (F.obj (RX.obj K)) ≫ QB.map (LY.map β₀) :=
      eLY.hom.naturality β₀
    simp only [Category.assoc]
    rw [reassoc_of% hf]
  have hr : s ≫ α.hom.app (RX'.obj (QA.obj K)) ≫
      G'.map (a.counit.app (QA.obj K)) =
    eLY.hom.app (F.obj (RX.obj K)) ≫
      QB.map (α₀ ≫ G.map εX) ≫ ηG.app K := by
    dsimp only [s]
    simp only [Functor.map_comp, Category.assoc]
    have hn : LY'.map (F'.map (ηRX.app K)) ≫ α.hom.app (RX'.obj (QA.obj K)) =
      α.hom.app (QX.obj (RX.obj K)) ≫ G'.map (LX'.map (ηRX.app K)) :=
      α.hom.naturality (ηRX.app K)
    rw [reassoc_of% hn]
    simp only [Functor.comp_obj, ← Functor.map_comp]
    rw [ha, Functor.map_comp]
    rw [reassoc_of% hα]
    have hg : QB.map (G.map εX) ≫ ηG.app K =
      ηG.app (LX.obj (RX.obj K)) ≫ G'.map (QA.map εX) :=
      ηG.naturality εX
    rw [← hg]
  rw [hl, hr, h₀]

/-- On a K-injective complex on the inverse-image open, restricting the normalized
composition comparison and then applying the base-open counit agrees with first
using the open-restriction comparison and then pushing forward the source-open counit.
The parameter β is fixed by hβ to the canonical composite. Keeping it as an
explicit parameter avoids unfolding its right-derived choice in each projection.
This concerns an arbitrary complex on the open, not a restriction unit on X.

Source: Stacks Project, Tags 08FE (sectionwise restriction/direct-image identity),
0D5T (composition of derived direct images), and 08BV (open adjunction computation).
Proof: Substitute the defining equality hβ. Let jX and jY be the two open
inclusions and g the restricted morphism.
Open direct image jX_* preserves K-injective complexes, since its left adjoint is
exact restriction. Thus I and jX_*I compute the relevant source derived images.
Use the determining right-derived unit equations of both composition comparisons
and jX followed by h = g followed by jY to identify the restricted composition
comparison with the localization of the sectionwise composition identity. Expand
schemeMVOpenRestrictionComparison using the unit factorization equations of its
exact-functor and composition factors. The required equality now reads, on an open
W of U, that the two counit identifications of sections of I over g inverse image W
are equal. Both are the restriction/direct-image identity of Tag 08FE, with the
open-adjunction counits identifying restriction of open direct image with I.
These equalities commute with differentials, so descend through the homotopy and
derived localizations. The factorization equation for the derived counit
(Adjunction.derivedε_fac_app) identifies the localized counits with the displayed
schemeMVAdjunction counits. Cancel the intervening computation isomorphisms.
For U empty both target objects are zero; for U top this is the normalized
composition identity. Neither a cover nor a unit at an object on X is used.
(blueprint: lem-pc-derived-mayer-vietoris-open-composition-counit). -/
theorem schemeMVOpenComposition_counit_Q
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    (schemeMVDerivedRestriction Y U).map
        (β.hom.app (DerivedCategory.Q.obj I)) ≫
        (schemeMVAdjunction Y U).counit.app
          ((schemeDerivedDirectImage (h ∣_ U)).obj (DerivedCategory.Q.obj I)) =
      (schemeMVOpenRestrictionComparison h U).hom.app
          ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj (DerivedCategory.Q.obj I)) ≫
        (schemeDerivedDirectImage (h ∣_ U)).map
          ((schemeMVAdjunction X (h ⁻¹ᵁ U)).counit.app (DerivedCategory.Q.obj I)) := by
  let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
  let RY := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
  let LY := schemeOpenRestriction Y U
  let a₀ : LX ⊣ RX := schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)
  let b₀ : LY ⊣ RY := schemeOpenModuleAdjunction Y U
  let a := schemeMVAdjunction X (h ⁻¹ᵁ U)
  let b := schemeMVAdjunction Y U
  let α := schemeMVOpenRestrictionComparison h U
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let RXh := RX.mapHomotopyCategory (ComplexShape.up ℤ)
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
  let RYh := RY.mapHomotopyCategory (ComplexShape.up ℤ)
  let α₀ := (schemeMVHomotopyOpenRestriction h U).hom.app (RXh.obj K)
  let β₀ := (schemeMVHomotopyOpenComposition h U).hom.app K
  let εX := ((a₀.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K)
  let εY := ((b₀.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app (Gh.obj K))
  have ha : LX.mapDerivedCategory.map (RX.rightDerivedFunctorUnit.app K) ≫
      a.counit.app (DerivedCategory.Qh.obj K) =
    LX.mapDerivedCategoryFactorsh.hom.app (RXh.obj K) ≫ DerivedCategory.Qh.map εX := by
    exact (a₀.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      LX.mapDerivedCategoryFactorsh.hom RX.rightDerivedFunctorUnit K
  have hb : LY.mapDerivedCategory.map (RY.rightDerivedFunctorUnit.app (Gh.obj K)) ≫
      b.counit.app (DerivedCategory.Qh.obj (Gh.obj K)) =
    LY.mapDerivedCategoryFactorsh.hom.app (RYh.obj (Gh.obj K)) ≫
      DerivedCategory.Qh.map εY := by
    exact (b₀.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      LY.mapDerivedCategoryFactorsh.hom RY.rightDerivedFunctorUnit (Gh.obj K)
  have hα := schemeMVOpenRestriction_unit_normalization X Y h U (RXh.obj K)
  have hβ' := schemeMVOpenComposition_unit_normalization X Y h U β hβ K
  have h₀ := schemeMVUnderivedOpenCounit_square X Y h U K
  have : RX.PreservesKInjectiveComplexes := a₀.preservesKInjectiveComplexes
  have hs : IsIso (F.rightDerivedFunctorUnit.app (RXh.obj K)) := by
    have : CochainComplex.IsKInjective
        ((RX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := inferInstance
    change IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((RX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    infer_instance
  have ht : IsIso (RX.rightDerivedFunctorUnit.app K) := by
    dsimp [K]
    infer_instance
  have hc := counit_of_unit_normalizations a b α β
    RX.rightDerivedFunctorUnit F.rightDerivedFunctorUnit
    G.rightDerivedFunctorUnit RY.rightDerivedFunctorUnit
    LX.mapDerivedCategoryFactorsh LY.mapDerivedCategoryFactorsh
    K α₀ β₀ εX εY ha hb hα hβ' h₀
  exact counit_transport a b F.rightDerivedFunctor G.rightDerivedFunctor α β
    ((DerivedCategory.quotientCompQhIso _).app I) hc

end AlgebraicGeometry
