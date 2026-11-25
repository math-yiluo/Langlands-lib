/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CanonicalPullbackSectionUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! The precomposition form of the canonical section/projection coherence. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

section ProjectionCalculus
open Functor.OplaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]

-- Use the same two symmetries as the canonical left-factor projection.
private def leftProjection {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.OplaxMonoidal] (M : C) (N : D) :
    M ⊗ G.obj N ⟶ G.obj (F.obj M ⊗ N) :=
  (β_ M (G.obj N)).hom ≫
    ((adj.rightAdjointProjectionMap (δNatTrans F)).app N).app M ≫
      G.map (β_ N (F.obj M)).hom

-- The middle pair of signed symmetries cancels before composing the mates.
private theorem leftProjection_comp
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal]
    {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G') [F'.OplaxMonoidal]
    (M : C) (N : E) :
    leftProjection adj M (G'.obj N) ≫ G.map (leftProjection adj' (F.obj M) N) =
      leftProjection (adj.comp adj') M N := by
  unfold leftProjection
  rw [adj.rightAdjointProjectionMap_comp adj' (δNatTrans F) (δNatTrans F')
    (δNatTrans (F ⋙ F')) (fun _ _ ↦ rfl)]
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj]
  rw [← G.map_comp_assoc (β_ (G'.obj N) (F.obj M)).hom,
    SymmetricCategory.symmetry, G.map_id, Category.id_comp]

-- Only the component of the section comparison at the tensor unit is needed.
private theorem leftProjection_section
    {F G : C ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal]
    (s : F ≅ 𝟭 C) (hunit : s.hom.app (𝟙_ C) = η F)
    (U : C) (e : U ≅ 𝟙_ C) (M : C) :
    (ρ_ M).inv ≫
      (M ◁ (e.inv ≫ (conjugateIsoEquiv Adjunction.id adj s).hom.app U)) ≫
      leftProjection adj M U ≫
      G.map (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom) =
        (conjugateIsoEquiv Adjunction.id adj s).hom.app M := by
  let b := (conjugateIsoEquiv Adjunction.id adj s).hom
  have hb (A : C) : F.map (b.app A) ≫ adj.counit.app A = s.hom.app A := by
    change F.map (((conjugateEquiv Adjunction.id adj) s.hom).app A) ≫
      adj.counit.app A = s.hom.app A
    have h := conjugateEquiv_counit Adjunction.id adj s.hom A
    change F.map (((conjugateEquiv Adjunction.id adj) s.hom).app A) ≫
      adj.counit.app A = s.hom.app A ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id _)
  change (ρ_ M).inv ≫ (M ◁ (e.inv ≫ b.app U)) ≫ leftProjection adj M U ≫
    G.map (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom) = b.app M
  unfold leftProjection
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj.counit_naturality, adj.counit_naturality_assoc,
    adj.counit_naturality_assoc, adj.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  change F.map (λ_ M).inv ≫ F.map (e.inv ▷ M) ≫ F.map (b.app U ▷ M) ≫
    δ F (G.obj U) M ≫ (adj.counit.app U ▷ F.obj M) ≫
    (β_ U (F.obj M)).hom ≫ tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom =
      F.map (b.app M) ≫ adj.counit.app M
  rw [← δ_natural_left_assoc, ← comp_whiskerRight_assoc, hb,
    ← BraidedCategory.braiding_naturality_assoc]
  simp only [Functor.id_obj]
  rw [braiding_rightUnitor, tensorHom_def_assoc, leftUnitor_naturality,
    ← comp_whiskerRight_assoc, ← δ_natural_left_assoc,
    ← comp_whiskerRight_assoc]
  have hu : F.map e.inv ≫ s.hom.app U ≫ e.hom = η F := by
    simpa only [Functor.id_map, Iso.inv_hom_id, Category.comp_id, hunit] using
      s.hom.naturality_assoc e.inv e.hom
  rw [hu, left_unitality_hom_assoc, ← F.map_comp_assoc, Iso.inv_hom_id,
    F.map_id, Category.id_comp, hb]

private theorem leftProjection_section_comp
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal]
    {F' : D ⥤ C} {G' : C ⥤ D} (adj' : F' ⊣ G') [F'.OplaxMonoidal]
    (s : F ⋙ F' ≅ 𝟭 C)
    (hunit : s.hom.app (𝟙_ C) = η (F ⋙ F'))
    (U : C) (e : U ≅ 𝟙_ C) (M : C) :
    (ρ_ M).inv ≫
      (M ◁ (e.inv ≫ (conjugateIsoEquiv Adjunction.id (adj.comp adj') s).hom.app U)) ≫
      leftProjection adj M (G'.obj U) ≫
      G.map (leftProjection adj' (F.obj M) U ≫
        G'.map (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom)) =
      (conjugateIsoEquiv Adjunction.id (adj.comp adj') s).hom.app M := by
  have h := leftProjection_section (adj.comp adj') s hunit U e M
  rw [← leftProjection_comp adj adj'] at h
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using h

end ProjectionCalculus

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] supportedUnitIso pushSectionIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

section NativeProjection
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory
attribute [local implicit_reducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
  tracePull tracePush
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.leftDerivedUpperStarComp CondensedRing.leftDerivedUpperStarId
  CondensedRing.leftDerivedUpperStarUnitIso

@[instance_reducible]
private def native_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 20001] native_sheaf_symmetric

attribute [-instance] internalMonoidal in
private local instance native_symmetric (X : Scheme.{u}) :
    SymmetricCategory (DerivedCategory (Modules Λ X)) :=
  DerivedCategory.symmetricCategory (Modules Λ X)

attribute [-instance] internalMonoidal in
private local instance native_oplax {X S : Scheme.{u}} (g : X ⟶ S) :
    (CondensedRing.upperStar Λ g).leftDerivedFunctor.OplaxMonoidal :=
  (CondensedRing.monoidal_leftDerivedUpperStar Λ g).toOplaxMonoidal

attribute [-instance] internalMonoidal in
private local instance native_wrapped_oplax {X S : Scheme.{u}} (g : X ⟶ S) :
    (moduleObjectDerivedPullback Λ g).OplaxMonoidal := by
  unfold moduleObjectDerivedPullback
  exact native_oplax Λ g

attribute [-instance] internalMonoidal in
private def native_adj {X S : Scheme.{u}} (g : X ⟶ S) :
    moduleObjectDerivedPullback Λ g ⊣ moduleObjectDerivedPushforward Λ g :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ g

attribute [-instance] internalMonoidal in
private theorem traceProjection_eq_leftProjection {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X)) :
    traceProjection Λ g K N =
      leftProjection (native_adj Λ g) K N := by
  unfold traceProjection traceBraiding traceDerivedBraiding moduleObjectProjectionMate
    leftProjection moduleObjectDerivedTensorComparison native_adj
  rfl

attribute [-instance] internalMonoidal in
private theorem native_section_unit {X S : Scheme.{u}} (g : X ⟶ S) (p : S ⟶ X)
    (h : g ≫ p = 𝟙 X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (hs : s = (CondensedRing.leftDerivedUpperStarComp Λ g p).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h) ≪≫
        CondensedRing.leftDerivedUpperStarId Λ X) :
    s.hom.app (𝟙_ (DerivedCategory (Modules Λ X))) =
      Functor.OplaxMonoidal.η
        (moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g) := by
  exact CondensedRing.leftDerivedUpperStarSection_hom_app_unit Λ g p h s hs

attribute [-instance] internalMonoidal in
private theorem native_projective_unit (Y : Scheme.{u}) :
    (pullSectionIso Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app (𝟙_ _) =
    Functor.OplaxMonoidal.η
      (moduleObjectDerivedPullback Λ (secondProjection Y) ⋙
        moduleObjectDerivedPullback Λ (diagonalImmersion Y)) := by
  exact native_section_unit Λ (diagonalImmersion Y) (secondProjection Y)
    (by unfold secondProjection; exact pullback.diagonal_snd _)
    (pullSectionIso Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _))
    (pullSectionIso_eq Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _))

attribute [-instance] internalMonoidal in
private theorem native_pushSection_component (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (conjugateIsoEquiv Adjunction.id
      ((native_adj Λ (secondProjection Y)).comp (native_adj Λ (diagonalImmersion Y)))
      (pullSectionIso Λ Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))).hom.app M =
      (pushSectionIso Λ Y).hom.app M := by
  unfold pushSectionIso native_adj
  rfl

attribute [-instance] internalMonoidal in
private theorem native_section_projection (Y : Scheme.{u})
    (U : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ (ProjectiveLine Y))))
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (ρ_ M).inv ≫ (M ◁ (e.inv ≫ (pushSectionIso Λ Y).hom.app U)) ≫
      traceProjection Λ (secondProjection Y) M
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj U) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (traceProjection Λ (diagonalImmersion Y)
          ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj M) U ≫
          (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).map
            (tensorHom
              ((pullSectionIso Λ Y (secondProjection Y)
                (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app M)
              e.hom ≫ (ρ_ M).hom)) = (pushSectionIso Λ Y).hom.app M := by
  have h := leftProjection_section_comp
    (native_adj Λ (secondProjection Y)) (native_adj Λ (diagonalImmersion Y))
    (pullSectionIso Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _))
    (native_projective_unit Λ Y) U e M
  simpa only [native_pushSection_component, ← traceProjection_eq_leftProjection] using h

end NativeProjection

attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory

private theorem normalized_section_projection
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a) (Y : Scheme.{u})
    (U : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ (ProjectiveLine Y))))
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (ρ_ M).inv ≫ (M ◁ (e.inv ≫ (pushSectionIso Λ Y).hom.app U)) ≫
      a (secondProjection Y) M
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj U) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (a (diagonalImmersion Y)
          ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj M) U ≫
          (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).map
            (tensorHom
              ((pullSectionIso Λ Y (secondProjection Y)
                (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app M)
              e.hom ≫ (ρ_ M).hom)) = (pushSectionIso Λ Y).hom.app M := by
  unfold ProjectionFamily ProjectionNormalized internalMonoidal internalTensorBundle
    nativeTensorBundle at *
  have he : @a =
      (fun {X S : Scheme.{u}} (f : X ⟶ S) K N ↦ traceProjection Λ f K N) := by
    funext X S f K N
    exact eq_of_heq (ha f K N)
  cases he
  exact native_section_projection Λ Y U e M

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/--
The categorical section/projection composite before postcomposition by the inverse
of the canonical pushforward comparison.
-/
theorem canonical_section_projection_core_precomposition
    (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    ((ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)))) ≫
      projectionMap Λ (secondProjection Y) M
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y))) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
          (pullSectionIso Λ Y (secondProjection Y)
            (by unfold secondProjection; exact pullback.diagonal_snd _))
          (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M)) =
      (pushSectionIso Λ Y).hom.app M := by
  unfold sectionTensorMap projectionMap
  simpa only [Category.assoc] using
    normalized_section_projection Λ (projection_existsUnique Λ).exists.choose
      (projection_existsUnique Λ).exists.choose_spec Y (unit Λ (ProjectiveLine Y))
      (singleUnitIso Λ (ProjectiveLine Y)) M

end AlgebraicGeometry.ProEtale.RationalP1
