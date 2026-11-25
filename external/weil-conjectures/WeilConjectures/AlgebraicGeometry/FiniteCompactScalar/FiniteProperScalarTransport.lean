/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteRealizationScalarMate
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteProperSiteAmbientNormalization

/-! # Scalar transport for the proper factor of compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

private def scalarTranspose
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (r : Rx ⋙ F ⟶ G ⋙ Ry) :
    F ⋙ Sy ⟶ Sx ⋙ G where
  app K := (ay.homEquiv _ _).symm
    (F.map (ax.unit.app K) ≫ r.app (Sx.obj K))
  naturality {K L} f := by
    apply (ay.homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [ay.homEquiv_naturality_left, ay.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [← Category.assoc, ← F.map_comp]
    have hu := ax.unit.naturality f
    change f ≫ ax.unit.app L = ax.unit.app K ≫ Rx.map (Sx.map f) at hu
    rw [hu]
    simp only [F.map_comp, Category.assoc]
    exact congrArg (fun q ↦ F.map (ax.unit.app K) ≫ q) (r.naturality (Sx.map f))

private theorem plusLowerBound (A : Type u) [CommRing A] (Z : Scheme.{u})
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    ∃ n : ℤ, H.obj.IsGE n := H.property

private def ambientProperSiteIso (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  (intrinsicSiteFunctorIso A Y).app _ ≪≫
    (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      (ProEtale.directImageComparisonAmbientIso
        (ULift.{u + 1, u} A) g H.obj (plusLowerBound A Z H)) ≪≫
    (sfIntrinsicDerivedDirectImageComparison g A).symm.app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).mapDerivedCategory.obj H.obj) ≪≫
    (proEtaleConstantDerivedDirectImage g A).mapIso
      ((intrinsicSiteFunctorIso A Z).app H.obj).symm

private theorem properSiteIso_eq_ambient (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    properSiteIso A g H = ambientProperSiteIso A g H := by
  apply Iso.ext
  simpa only [ambientProperSiteIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, ProEtale.directImageComparisonAmbientIso, asIso_hom]
    using properSiteIso_hom_ambient A g H

private theorem fixedSiteScalar_mate_with_iso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (HB : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eHB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj H.obj ≅
      HB.obj) :
    (mateEquiv
      (ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
      (ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
      (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) g).hom)).app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).mapDerivedCategory.obj H.obj) ≫
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor.map
          ((ProEtale.pbcComparisonReduction Z
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom.app H.obj ≫
              (ProEtale.comparisonUpperStar
                (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Z).mapDerivedCategory.map eHB.hom) =
    (ProEtale.pbcFixedScalarExtension (ProEt.topology Y)
      (RingHom.ulift.{u + 1, u + 1, u, u} φ)).map
        (ProEtale.directImageComparisonAmbientIso
          (ULift.{u + 1, u} A) g H.obj (plusLowerBound A Z H)).inv ≫
      (ProEtale.pbcComparisonReduction Y
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom.app
          ((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor.obj H.obj) ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
          ((Etale.scalarMate (RingHom.ulift.{u + 1, u + 1, u, u} φ) g).app H.obj ≫
            (Etale.lowerStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor.map eHB.hom) ≫
      (ProEtale.directImageComparisonAmbient (ULift.{u + 1, u} B) g).app HB.obj := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let NA := fun T : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
  let NB := fun T : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory
  let QB := (ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor
  let RA := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor
  let RB := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor
  let TY := ProEtale.pbcFixedScalarExtension (ProEt.topology Y) a
  let γ := (mateEquiv
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
    (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso a g).hom))
  let δX := ProEtale.pbcComparisonReduction Z a
  let δY := ProEtale.pbcComparisonReduction Y a
  let βA := ProEtale.directImageComparisonAmbientIso
    (ULift.{u + 1, u} A) g H.obj (plusLowerBound A Z H)
  let βB := ProEtale.directImageComparisonAmbient (ULift.{u + 1, u} B) g
  have hBJ : ∃ n : ℤ, ((Etale.scalarExtension a Z).obj H.obj).IsGE n := by
    obtain ⟨n, hn⟩ := HB.property
    have := hn
    exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso eHB.symm n⟩
  have hf := ProEtale.etaleProEtale_scalar_mate a g H.obj H.property hBJ
  have hf' : γ.app ((NA Z).obj H.obj) ≫
      QB.map (δX.hom.app H.obj ≫ (NB Z).map eHB.hom) =
      TY.map βA.inv ≫ δY.hom.app (RA.obj H.obj) ≫
        (NB Y).map ((Etale.scalarMate a g).app H.obj ≫ RB.map eHB.hom) ≫
        βB.app HB.obj := by
    have hn := βB.naturality eHB.hom
    dsimp only [Functor.comp_map] at hn
    have hfe : γ.app ((NA Z).obj H.obj) ≫ QB.map (δX.hom.app H.obj) =
        TY.map βA.inv ≫ δY.hom.app (RA.obj H.obj) ≫
          (NB Y).map ((Etale.scalarMate a g).app H.obj) ≫
          βB.app ((Etale.scalarExtension a Z).obj H.obj) := by
      simpa only [γ, NA, QB, TY, βA, βB, δX, δY, RA, NB,
        ProEtale.scalarPullbackEtaleIso, Etale.scalarMate] using hf
    have hh := congrArg (fun t ↦ t ≫ QB.map ((NB Z).map eHB.hom)) hfe
    simp only [Category.assoc] at hh
    erw [← hn] at hh
    simpa only [Functor.map_comp, Category.assoc] using hh
  exact hf'

/-- Proper direct-image scalar transport in intrinsic coordinates. This compares
only proper images, before composing with any extension by zero.

Source: Stacks Tags 0D6E, 0D6J, 099R and 0GL6; blueprint scalar-six direct-image
proof, finite rings paragraph; compact-support constructibility, Step 5.
(blueprint: lem-finite-proper-scalar-transport).

Proof: compute the intrinsic realization/restriction square on a K-injective
B-complex J and a K-injective resolution of its restriction. The normalization
of sfDerivedImageRestriction identifies its component with the inverse image
of the resolution arrow. The normalization of
sfIntrinsicDerivedDirectImageComparison gives the same equation after
realization. The sectionwise underived squares commute, so cancel the common
quasi-isomorphism to identify the intrinsic restriction square with the
fixed-scalar one. Transpose under the coefficient adjunction; its comparison
is realizationScalarIso by left-adjoint uniqueness. On fixed-scalar sites,
apply etaleProEtale_scalar_mate at H.obj. Its boundedness hypothesis is H's
lower bound, and its scalar-extension lower bound follows from eHB and HB.
The canonical inverse pullback scalar mate is scalarPullbackIso, by its
K-flat normalization. The D+ direct-image comparison used in properSiteIso
is the same counit mate as its ambient comparison, by compatibility of
derived adjunctions with the inclusion. Whisker the equation by realization
and cancel the site/realization unit and counit maps. Naturality inserts eHB.
This uses no flatness or additional boundedness on the target scalar extension;
zero rings, empty schemes and identity maps obey the same unit equations. -/
theorem properScalar_transport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]
    [IsNoetherian Z] [IsNoetherian Y]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (HB : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eHB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj H.obj ≅
      HB.obj) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Y)).homEquiv _ _).symm
        ((proEtaleConstantDerivedDirectImage g A).map
            ((pbcDerivedScalarAdjunction (scalarRingMap φ Z)).unit.app
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison Z A).obj H.obj)) ≫
          (sfDerivedImageRestriction g φ).hom.app
            ((pbcDerivedExtend (scalarRingMap φ Z)).obj
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison Z A).obj H.obj))) ≫
      (proEtaleConstantDerivedDirectImage g B).map
        ((siteScalarIso φ Z).hom.app H.obj ≫
          (ProEtale.finiteCoefficientIntrinsicDerivedComparison Z B).map eHB.hom) =
    (pbcDerivedExtend (scalarRingMap φ Y)).map (properSiteIso A g H).inv ≫
      (siteScalarIso φ Y).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor.obj
          H.obj) ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).map
        ((Etale.scalarMate (RingHom.ulift.{u + 1, u + 1, u, u} φ) g).app H.obj ≫
          (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor.map
            eHB.hom) ≫
      (properSiteIso B g HB).hom := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let NA := fun T : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
  let NB := fun T : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory
  let EA := sfIntrinsicDerivedEquivalence Z A
  let EB := sfIntrinsicDerivedEquivalence Z B
  let FB := sfIntrinsicDerivedEquivalence Y B
  let PA := proEtaleConstantDerivedDirectImage g A
  let PB := proEtaleConstantDerivedDirectImage g B
  let QA := (ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor
  let QB := (ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor
  let RA := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor
  let RB := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor
  let SY := pbcDerivedExtend (scalarRingMap φ Y)
  let TX := ProEtale.pbcFixedScalarExtension (ProEt.topology Z) a
  let TY := ProEtale.pbcFixedScalarExtension (ProEt.topology Y) a
  let α := scalarTranspose (pbcDerivedScalarAdjunction (scalarRingMap φ Z))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y)) PA PB (sfDerivedImageRestriction g φ).hom
  let γ := (mateEquiv
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
    (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso a g).hom))
  let δX := ProEtale.pbcComparisonReduction Z a
  let δY := ProEtale.pbcComparisonReduction Y a
  let βA := ProEtale.directImageComparisonAmbientIso
    (ULift.{u + 1, u} A) g H.obj (plusLowerBound A Z H)
  let βB := ProEtale.directImageComparisonAmbient (ULift.{u + 1, u} B) g
  let dA := sfIntrinsicDerivedDirectImageComparison g A
  let dB := sfIntrinsicDerivedDirectImageComparison g B
  let rX := realizationScalarIso φ Z
  let rY := realizationScalarIso φ Y
  have hf' : γ.app ((NA Z).obj H.obj) ≫
      QB.map (δX.hom.app H.obj ≫ (NB Z).map eHB.hom) =
      TY.map βA.inv ≫ δY.hom.app (RA.obj H.obj) ≫
        (NB Y).map ((Etale.scalarMate a g).app H.obj ≫ RB.map eHB.hom) ≫
        βB.app HB.obj := by
    exact fixedSiteScalar_mate_with_iso φ g H HB eHB
  have hr : α.app (EA.functor.obj ((NA Z).obj H.obj)) ≫
      PB.map (rX.hom.app ((NA Z).obj H.obj)) ≫ dB.hom.app (TX.obj ((NA Z).obj H.obj)) =
      SY.map (dA.hom.app ((NA Z).obj H.obj)) ≫
        rY.hom.app (QA.obj ((NA Z).obj H.obj)) ≫
        FB.functor.map (γ.app ((NA Z).obj H.obj)) := by
    exact realizationScalar_directImage_mate φ g ((NA Z).obj H.obj)
  have hr' : α.app (EA.functor.obj ((NA Z).obj H.obj)) ≫
      PB.map (rX.hom.app ((NA Z).obj H.obj)) =
      SY.map (dA.hom.app ((NA Z).obj H.obj)) ≫
        rY.hom.app (QA.obj ((NA Z).obj H.obj)) ≫
        FB.functor.map (γ.app ((NA Z).obj H.obj)) ≫
        dB.inv.app (TX.obj ((NA Z).obj H.obj)) := by
    have hh := hr
    simp only [← Category.assoc] at hh
    have h := (Iso.eq_comp_inv (dB.app (TX.obj ((NA Z).obj H.obj)))).2 hh
    simpa only [Category.assoc, Iso.app_inv] using h
  have hBX := (intrinsicSiteFunctorIso B Z).inv.naturality eHB.hom
  dsimp only [Functor.comp_map] at hBX
  have hBXP := congrArg PB.map hBX
  simp only [PB.map_comp] at hBXP
  have hBY := (intrinsicSiteFunctorIso B Y).inv.naturality
    ((Etale.scalarMate a g).app H.obj ≫ RB.map eHB.hom)
  dsimp only [Functor.comp_map] at hBY
  have hd := dB.inv.naturality (δX.hom.app H.obj ≫ (NB Z).map eHB.hom)
  dsimp only [Functor.comp_map] at hd
  have hn := rY.hom.naturality βA.inv
  dsimp only [Functor.comp_map] at hn
  have hα := α.naturality ((intrinsicSiteFunctorIso A Z).hom.app H.obj)
  dsimp only [Functor.comp_map] at hα
  rw [properSiteIso_eq_ambient, properSiteIso_eq_ambient]
  change α.app _ ≫ PB.map _ = _
  simp only [siteScalarIso, ambientProperSiteIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    ProEtale.directImageComparisonAmbientIso, asIso_hom,
    Functor.id_obj, Functor.comp_obj, Category.id_comp, Category.assoc]
  erw [← hBXP]
  rw [← (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).map_comp_assoc]
  erw [← reassoc_of% hBY]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← SY.map_comp_assoc ((intrinsicSiteFunctorIso A Y).inv.app (RA.obj H.obj))
    ((intrinsicSiteFunctorIso A Y).hom.app (RA.obj H.obj))]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% hα, reassoc_of% hr']
  rw [← PB.map_comp_assoc, ← EB.functor.map_comp]
  erw [← reassoc_of% hd]
  rw [← FB.functor.map_comp_assoc, hf']
  simp only [FB.functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  simp only [PA, PB, SY, dA, dB, NA, NB, βA, βB, rY, FB, δY, RA, RB, a,
    ProEtale.directImageComparisonAmbientIso]

end AlgebraicGeometry.Scheme.FiniteCompactScalar
