/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.AlgebraicGeometry.SfIdentityProjectionNormalization
import WeilConjectures.AlgebraicGeometry.SfProperProjectionComposition

/-! # Projection along a proper section

Source: Stacks Project, Tags 0B56 and 0DV0; blueprint latest,
thm-amb-p1-adjunction.proof.md, projection naturality along the diagonal.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SupportedTrace

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The canonical direct-image identification for a proper section.
Source: Stacks Project, Tag 0DV0, composition and identity comparisons
(auxiliary; not a blueprint node). -/
def properSectionPushIso {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X) :
    𝟭 (DerivedCategoryModule A X) ≅ push A s ⋙ push A p :=
  (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).symm ≪≫
    rightDerivedLowerShriekCongrIso A h.symm ≪≫ rightDerivedLowerShriekCompIso A s p

/-- The tensor-unit description of pushforward along a proper section.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the diagonal unit description
(auxiliary; not a blueprint node). -/
def properSectionTensorIso {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X) :
    push A s ≅ CoordinateTrace.pull A p ⋙
      (derivedTensor (ModuleCat.{u + 1} A) W).obj
        ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X)) :=
  ((Functor.leftUnitor (push A s)).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).symm (push A s) ≪≫
    Functor.associator (CoordinateTrace.pull A p) (CoordinateTrace.pull A s) (push A s)) ≪≫
      Functor.isoWhiskerLeft (CoordinateTrace.pull A p) (projectionUnitIso A s)

open MonoidalCategory in
private theorem canonicalSymmetry_rightUnitInv
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasDerivedCategory.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (K : DerivedCategory B) :
    (ρ_ K).inv ≫
      ((_root_.DerivedCategory.canonicalTensorSymmetry B).hom.app K).app (𝟙_ _) =
        (λ_ K).inv := by
  let := _root_.DerivedCategory.braidedCategory' B
  exact CategoryTheory.rightUnitor_inv_braiding K

universe v

private theorem unit_symmetry_general
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (unitRightUnitor B X M).inv ≫
      ((derivedTensorSymmetry B X).hom.app M).app (derivedTensorUnit B X) =
      (derivedTensorUnitLeftUnitor B X).inv.app M := by
  unfold unitRightUnitor derivedTensorRightUnitor derivedTensorUnitLeftUnitor
    derivedTensorLeftUnitorNatIso derivedTensorLeftUnitor derivedTensorSymmetry
    derivedTensorUnit
  exact @canonicalSymmetry_rightUnitInv _ _ _ _ _
    (Etale.sheafMonoidalCategory B X) _ (Etale.sheafBraidedCategory B X)
    (Etale.sheafMonoidalClosed B X) _ M

section Proof

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor derivedTensorSymmetry
  rightDerivedLowerShriekCompIso rightDerivedLowerShriekCongrIso
  rightDerivedLowerShriekIdIsoOfLowerStar leftDerivedUpperStarComp leftDerivedUpperStarId
  properSectionPushIso properSectionTensorIso projectionUnitIso lowerStar upperStar
  leftDerivedUpperStarCompSectionIso
attribute [local implicit_reducible] rightDerivedLowerShriek

private theorem section_projection_forward {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X)
    (V M : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((properSectionPushIso A s p h).hom.app V)).app M ≫
      (projectionIso A p ((push A s).obj V)).hom.app M ≫
      (push A p).map ((projectionIso A s V).hom.app ((CoordinateTrace.pull A p).obj M)) ≫
      (push A p).map ((push A s).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
          ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M))) =
      (properSectionPushIso A s p h).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj M) := by
  let k := rightDerivedLowerShriekCongrIso A h.symm ≪≫ rightDerivedLowerShriekCompIso A s p
  have hc := properProjectionCompositionOfEq A s p (𝟙 X) h.symm V M
  have hn := k.hom.naturality
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M))
  dsimp only [k, Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  have he : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s p (𝟙 X) h.symm).hom.app M ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M := by
    simp -implicitDefEqProofs only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  simp -implicitDefEqProofs only [properSectionPushIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  change ((derivedTensor (ModuleCat.{u + 1} A) X).map
      ((rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).inv.app V ≫
        k.hom.app V)).app M ≫ _ =
    (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).inv.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj M) ≫ k.hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj M)
  rw [Functor.map_comp, NatTrans.comp_app]
  simp -implicitDefEqProofs only [Category.assoc]
  rw [reassoc_of% hc, ← hn]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, he]
  rw [reassoc_of% (identityProjectionNormalization A X V M)]

private theorem section_tensor_inv_generic
    {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) (L : C ⥤ D) (R : D ⥤ C)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (I : C)
    (l : T.obj I ≅ 𝟭 C) (e : L ⋙ R ≅ 𝟭 C)
    (π : U.obj (S.obj I) ≅ R ⋙ T.obj I ⋙ S)
    (γ : R ⋙ S ≅ U.obj (S.obj I)) (κ : S ≅ L ⋙ U.obj (S.obj I))
    (hγ : γ = Functor.isoWhiskerLeft R (Functor.isoWhiskerRight l.symm S) ≪≫ π.symm)
    (hκ : κ = ((Functor.leftUnitor S).symm ≪≫ Functor.isoWhiskerRight e.symm S ≪≫
      Functor.associator L R S) ≪≫ Functor.isoWhiskerLeft L γ) (M : C) :
    κ.inv.app M =
      π.hom.app (L.obj M) ≫ S.map (l.hom.app (R.obj (L.obj M))) ≫
        S.map (e.hom.app M) := by
  rw [hκ, hγ]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Category.comp_id, Category.assoc, Functor.comp_obj, Functor.id_obj]

private theorem section_tensor_inv {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X) (M : DerivedCategoryModule A X) :
    (properSectionTensorIso A s p h).inv.app M =
      (projectionIso A s (derivedTensorUnit (ModuleCat.{u + 1} A) X)).hom.app
        ((CoordinateTrace.pull A p).obj M) ≫
      (push A s).map ((derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) X).hom.app
        ((CoordinateTrace.pull A s).obj ((CoordinateTrace.pull A p).obj M))) ≫
      (push A s).map
        ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M) := by
  exact section_tensor_inv_generic (push A s) (CoordinateTrace.pull A p)
    (CoordinateTrace.pull A s) (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} A) W) (derivedTensorUnit (ModuleCat.{u + 1} A) X)
    (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) X)
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h)
    (projectionIso A s (derivedTensorUnit (ModuleCat.{u + 1} A) X))
    (projectionUnitIso A s) (properSectionTensorIso A s p h)
    (by unfold projectionUnitIso; rfl) (by unfold properSectionTensorIso; rfl) M

private theorem inverse_unit_square {C : Type*} [Category C] {V W Y Z : C}
    (l : V ≅ W) (k : Y ≅ Z) (a : V ⟶ Z) (b : W ⟶ Y)
    (h : a ≫ k.inv = l.hom ≫ b) : b ≫ k.hom = l.inv ≫ a := by
  apply (cancel_mono k.inv).1
  simp -implicitDefEqProofs only [Category.assoc, Iso.hom_inv_id, Category.comp_id, h,
    Iso.inv_hom_id_assoc]

private theorem unit_square_generic
    {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) (P : D ⥤ C) (Ls : D ⥤ C) (Lp : C ⥤ D)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (I : C)
    (L : T.obj I ≅ 𝟭 C) (e : Lp ⋙ Ls ≅ 𝟭 C) (α : 𝟭 C ≅ S ⋙ P)
    (κ : S ≅ Lp ⋙ U.obj (S.obj I))
    (pf : U.obj (S.obj I) ⟶ Ls ⋙ T.obj I ⋙ S)
    (pg : T.obj (P.obj (S.obj I)) ⟶ Lp ⋙ U.obj (S.obj I) ⋙ P) (M : C)
    (hf : (T.map (α.hom.app I)).app M ≫ pg.app M ≫
        P.map (pf.app (Lp.obj M)) ≫ P.map (S.map ((T.obj I).map (e.hom.app M))) =
      α.hom.app ((T.obj I).obj M))
    (hκ : κ.inv.app M = pf.app (Lp.obj M) ≫
      S.map (L.hom.app (Ls.obj (Lp.obj M))) ≫ S.map (e.hom.app M)) :
    α.hom.app M ≫ P.map (κ.hom.app M) =
      L.inv.app M ≫ (T.map (α.hom.app I)).app M ≫ pg.app M := by
  have hn := α.hom.naturality (L.hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj,
    Functor.comp_obj] at hn
  have hl := L.hom.naturality (e.hom.app M)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hl
  have hh := congrArg (fun v ↦ v ≫ P.map (S.map (L.hom.app M))) hf
  simp only [Category.assoc] at hh
  have hl' := congrArg (fun v ↦ P.map (S.map v)) hl
  simp only [Functor.map_comp] at hl'
  rw [hl', ← hn] at hh
  apply inverse_unit_square (L.app M) (P.mapIso (κ.app M))
    ((T.map (α.hom.app I)).app M ≫ pg.app M) (α.hom.app M)
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, hκ,
    Functor.map_comp, Category.assoc] using hh

private theorem section_unit_unordered {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X) (M : DerivedCategoryModule A X) :
    (properSectionPushIso A s p h).hom.app M ≫
      (push A p).map ((properSectionTensorIso A s p h).hom.app M) =
    (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) X).inv.app M ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((properSectionPushIso A s p h).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X))).app M ≫
      (projectionIso A p ((push A s).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X))).hom.app M := by
  exact unit_square_generic (push A s) (push A p) (CoordinateTrace.pull A s)
    (CoordinateTrace.pull A p) (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} A) W) (derivedTensorUnit (ModuleCat.{u + 1} A) X)
    (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) X)
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h)
    (properSectionPushIso A s p h) (properSectionTensorIso A s p h)
    (projectionIso A s (derivedTensorUnit (ModuleCat.{u + 1} A) X)).hom
    (projectionIso A p ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))).hom M
    (section_projection_forward A s p h (derivedTensorUnit (ModuleCat.{u + 1} A) X) M)
    (section_tensor_inv A s p h M)

omit [Finite A] in
private theorem symmetry_unit (X : Scheme.{u}) (M : DerivedCategoryModule A X) :
    (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
      (CoordinateTrace.swap A X M (derivedTensorUnit (ModuleCat.{u + 1} A) X)).hom =
      (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) X).inv.app M := by
  exact unit_symmetry_general (ModuleCat.{u + 1} A) X M

-- Assemble the public identity with the proof-local component instances.
private theorem properSectionProjectionUnit_proof {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X) (M : DerivedCategoryModule A X) :
    (properSectionPushIso A s p h).hom.app M ≫
        (push A p).map
          ((properSectionTensorIso A s p h).hom.app M ≫
            (CoordinateTrace.swap A W
              ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))
              ((CoordinateTrace.pull A p).obj M)).hom) =
      (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((properSectionPushIso A s p h).hom.app
            (derivedTensorUnit (ModuleCat.{u + 1} A) X)) ≫
        (orderedProjection A p M
          ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))).hom := by
  have hu := section_unit_unordered A s p h M
  have hn := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).naturality
    ((properSectionPushIso A s p h).hom.app
      (derivedTensorUnit (ModuleCat.{u + 1} A) X))
  change ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map _ ≫
      (CoordinateTrace.swap A X M _).hom =
    (CoordinateTrace.swap A X M _).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map _).app M at hn
  simp -implicitDefEqProofs only [orderedProjection, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp]
  rw [reassoc_of% hu, reassoc_of% hn, reassoc_of% (symmetry_unit A X M)]

end Proof

/-- Projection along a proper section carries insertion of its unit to the right unitor.
Source: Stacks Project, Tags 0B56 and 0DV0; blueprint latest,
thm-amb-p1-adjunction.proof.md, projection naturality in the two coordinate computations
(auxiliary; not a blueprint node).

Proof: apply composition coherence of the canonical projection maps to s followed by p. Use the
canonical identification of s*(p*M) with M and its conjugate direct-image comparison to
identify the composite projection with identity projection. Specialize the inside factor to
1_X. Its left unitor is the one used in projectionUnitIso. Naturality of that unitor and the
pullback section comparison rewrite the first projection as the displayed map from s!(s*(p*M))
to s!1_X tensor p*M. Conjugate the projections by their canonical symmetries to put M first.
The middle symmetries cancel. Identity projection followed by the left-unit symmetry is the
inverse right unitor of M. This proves the displayed formula before inverting the projection
for p, so no trace or diagonal class is used. Transport projection composition through the
proper forget-supports comparisons to obtain the chosen rightDerivedLowerShriek compositors and
identity comparison. -/
theorem properSectionProjectionUnit {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X) (M : DerivedCategoryModule A X) :
    (properSectionPushIso A s p h).hom.app M ≫
        (push A p).map
          ((properSectionTensorIso A s p h).hom.app M ≫
            (CoordinateTrace.swap A W
              ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))
              ((CoordinateTrace.pull A p).obj M)).hom) =
      (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((properSectionPushIso A s p h).hom.app
            (derivedTensorUnit (ModuleCat.{u + 1} A) X)) ≫
        (orderedProjection A p M
          ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))).hom := by
  exact properSectionProjectionUnit_proof A s p h M

end AlgebraicGeometry.Etale.SupportedTrace
