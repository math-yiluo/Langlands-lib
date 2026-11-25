/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.IndependentDerivedCube.IndependentDerivedCube
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.Right.RightDerivedExactRestrictionNormalization

/-! # Transport a commuting cube through equivalences

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-equivalence-cube-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.EquivalenceCubeTransport
universe u wA wB wC wD

/-- The canonical derived equivalence, with its two functors exposed as record fields.
Source: the canonical exact-functor localization of an equivalence.
(blueprint: lem-sf-equivalence-cube-transport).
The unit, counit and triangle equation are those of mapDerivedCategory. -/
@[implicit_reducible] def liftEquivalence
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] :
    DerivedCategory A ≌ DerivedCategory B where
  functor := e.functor.mapDerivedCategory
  inverse := e.inverse.mapDerivedCategory
  unitIso := e.mapDerivedCategory.unitIso
  counitIso := e.mapDerivedCategory.counitIso
  functor_unitIso_comp := e.mapDerivedCategory.functor_unitIso_comp

section
variable {A B C D : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} C] [Category.{u} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (eU : C ≌ A) (eV : D ≌ B)
  [F.Additive] [G.Additive] [eU.functor.Additive] [eV.functor.Additive]
  (c : F ⋙ eV.inverse ≅ eU.inverse ⋙ G)
/-- Right derive an inverse-equivalence direct-image comparison.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-equivalence-cube-transport). -/
def inverseDerivedPush :
    F.rightDerivedFunctor ⋙ eV.inverse.mapDerivedCategory ≅
      eU.inverse.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F eV.inverse).symm ≪≫
    Functor.rightDerivedFunctorNatIso c ≪≫
      Functor.rightDerivedFunctorCompIso eU.inverse G ≪≫
        Functor.isoWhiskerRight eU.inverse.rightDerivedFunctorIsoMapDerivedCategory
          G.rightDerivedFunctor
/-- This comparison has the canonical full cochain-unit normalization.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-equivalence-cube-transport).
Proof: specialize the proved exact-restriction normalization to the two inverse
equivalences. Its composite is exactly inverseDerivedPush. -/
theorem inverseDerivedPush_normalized :
    IndependentDerivedCube.unitNormalized F G eU.inverse eV.inverse
      eU.inverse.mapDerivedCategory eV.inverse.mapDerivedCategory
      eU.inverse.mapDerivedCategoryFactors eV.inverse.mapDerivedCategoryFactors
      c.hom (inverseDerivedPush F G eU eV c).hom := by
  intro I
  exact rightDerivedExactRestriction_normalization F G eU.inverse eV.inverse c I
end

/-- Recover the forward comparison by full faithfulness of the inverse equivalence.
Source: the unit equations of an equivalence.
(blueprint: lem-sf-equivalence-cube-transport). -/
def forwardOfInverse
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (eA : A ≌ C) (eB : B ≌ D) (F : A ⥤ B) (G : C ⥤ D)
    (h : G ⋙ eB.inverse ≅ eA.inverse ⋙ F) :
    F ⋙ eB.functor ≅ eA.functor ⋙ G :=
  (eB.fullyFaithfulInverse.whiskeringRight A).preimageIso
    (Functor.isoWhiskerLeft F eB.unitIso.symm ≪≫
      Functor.isoWhiskerRight eA.unitIso F ≪≫ Functor.isoWhiskerLeft eA.functor h.symm)

private theorem forwardOfInverse_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (eA : A ≌ C) (eB : B ≌ D) (F : A ⥤ B) (G : C ⥤ D)
    (h : G ⋙ eB.inverse ≅ eA.inverse ⋙ F) (N : A) :
    eB.inverse.map ((forwardOfInverse eA eB F G h).hom.app N) ≫
        h.hom.app (eA.functor.obj N) =
      eB.unitIso.inv.app (F.obj N) ≫ F.map (eA.unitIso.hom.app N) := by
  have hf := (eB.fullyFaithfulInverse.whiskeringRight A).map_preimage
    (X := F ⋙ eB.functor) (Y := eA.functor ⋙ G)
    (Functor.isoWhiskerLeft F eB.unitIso.symm ≪≫
      Functor.isoWhiskerRight eA.unitIso F ≪≫
        Functor.isoWhiskerLeft eA.functor h.symm).hom
  have hh := NatTrans.congr_app hf N
  change eB.inverse.map ((forwardOfInverse eA eB F G h).hom.app N) = _ at hh
  rw [hh]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- An inverse-presentation cube gives the corresponding forward-presentation cube.
Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; formal equivalence transport.
(blueprint: lem-sf-equivalence-cube-transport).
Proof: apply the faithful inverse functor and postcompose with the inverse cube's
isomorphisms. Naturality moves the four comparison maps through the cube. Their unit
equations cancel each equivalence unit; canceling the remaining isomorphisms proves
the displayed forward equation. No derived or scalar-extension hypothesis is needed. -/
theorem forwardCube
    {A0 A1 B0 B1 C0 C1 D0 D1 : Type*}
    [Category A0] [Category A1] [Category B0] [Category B1]
    [Category C0] [Category C1] [Category D0] [Category D1]
    (eA0 : A0 ≌ C0) (eA1 : A1 ≌ C1) (eB0 : B0 ≌ D0) (eB1 : B1 ≌ D1)
    (rU : A0 ⥤ A1) (rV : B0 ⥤ B1) (qS : A0 ⥤ B0) (qR : A1 ⥤ B1)
    (cU : C0 ⥤ C1) (cV : D0 ⥤ D1) (pC : C0 ⥤ D0) (pI : C1 ⥤ D1)
    (kU : cU ⋙ eA1.inverse ≅ eA0.inverse ⋙ rU)
    (kV : cV ⋙ eB1.inverse ≅ eB0.inverse ⋙ rV)
    (x : pI ⋙ eB1.inverse ≅ eA1.inverse ⋙ qR)
    (y : pC ⋙ eB0.inverse ≅ eA0.inverse ⋙ qS)
    (d : qS ⋙ rV ≅ rU ⋙ qR) (b : pC ⋙ cV ≅ cU ⋙ pI)
    (h : ∀ M : C0,
      kV.hom.app (pC.obj M) ≫ rV.map (y.hom.app M) ≫ d.hom.app (eA0.inverse.obj M) =
        eB1.inverse.map (b.hom.app M) ≫ x.hom.app (cU.obj M) ≫ qR.map (kU.hom.app M))
    (N : A0) :
    eB1.functor.map (d.inv.app N) ≫
        (forwardOfInverse eB0 eB1 rV cV kV).hom.app (qS.obj N) ≫
        cV.map ((forwardOfInverse eA0 eB0 qS pC y).hom.app N) =
      (forwardOfInverse eA1 eB1 qR pI x).hom.app (rU.obj N) ≫
        pI.map ((forwardOfInverse eA0 eA1 rU cU kU).hom.app N) ≫
        b.inv.app (eA0.functor.obj N) := by
  apply eB1.inverse.map_injective
  apply (cancel_mono (eB1.inverse.map (b.hom.app (eA0.functor.obj N)) ≫
    x.hom.app (cU.obj (eA0.functor.obj N)) ≫
      qR.map (kU.hom.app (eA0.functor.obj N)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← h (eA0.functor.obj N)]
  rw [reassoc_of% kV.hom.naturality
    ((forwardOfInverse eA0 eB0 qS pC y).hom.app N)]
  rw [reassoc_of% forwardOfInverse_unit eB0 eB1 rV cV kV (qS.obj N)]
  rw [← rV.map_comp_assoc
    (eB0.inverse.map ((forwardOfInverse eA0 eB0 qS pC y).hom.app N))
    (y.hom.app (eA0.functor.obj N)), forwardOfInverse_unit eA0 eB0 qS pC y N]
  simp only [rV.map_comp, Category.assoc]
  rw [← rV.map_comp_assoc, Iso.hom_inv_id_app]
  erw [rV.map_id, Category.id_comp]
  rw [reassoc_of% eB1.unitIso.inv.naturality (d.inv.app N)]
  have hd := d.hom.naturality (eA0.unitIso.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hd
  rw [hd]
  rw [h (eA0.functor.obj N)]
  -- Reduce the other path using the same unit equations.
  rw [← eB1.inverse.map_comp_assoc
    (b.inv.app (eA0.functor.obj N)) (b.hom.app (eA0.functor.obj N)), Iso.inv_hom_id_app]
  simp only [eB1.inverse.map_id, Category.id_comp]
  rw [reassoc_of% x.hom.naturality
    ((forwardOfInverse eA0 eA1 rU cU kU).hom.app N)]
  rw [reassoc_of% forwardOfInverse_unit eA1 eB1 qR pI x (rU.obj N)]
  rw [← qR.map_comp
    (eA1.inverse.map ((forwardOfInverse eA0 eA1 rU cU kU).hom.app N))
    (kU.hom.app (eA0.functor.obj N)), forwardOfInverse_unit eA0 eA1 rU cU kU N]
  simp only [qR.map_comp]
  rw [← qR.map_comp_assoc, Iso.hom_inv_id_app]
  erw [qR.map_id, Category.id_comp]
  simp only [Functor.id_obj, Iso.inv_hom_id_app_assoc]

-- The unit and normalization lemmas above form the interface to these constructions.
attribute [irreducible] inverseDerivedPush forwardOfInverse

end CategoryTheory.EquivalenceCubeTransport
