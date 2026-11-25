/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarTransport
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteProperScalarTransport

/-! # Canonical transport of the finite compact-support scalar mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

private theorem scalar_transpose_paste
    {C₀ C₁ Z₀ Z₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category Z₀] [Category Z₁]
    [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sz : Z₀ ⥤ Z₁} {Rz : Z₁ ⥤ Z₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (az : Sz ⊣ Rz) (ay : Sy ⊣ Ry)
    (J₀ : C₀ ⥤ Z₀) (J₁ : C₁ ⥤ Z₁)
    (P₀ : Z₀ ⥤ D₀) (P₁ : Z₁ ⥤ D₁)
    (j : Rx ⋙ J₀ ⟶ J₁ ⋙ Rz) (p : Rz ⋙ P₀ ⟶ P₁ ⋙ Ry)
    (K : C₀) :
    (ay.homEquiv _ _).symm
      (P₀.map (J₀.map (ax.unit.app K)) ≫
        P₀.map (j.app (Sx.obj K)) ≫ p.app (J₁.obj (Sx.obj K))) =
      (ay.homEquiv _ _).symm
        (P₀.map (az.unit.app (J₀.obj K)) ≫ p.app (Sz.obj (J₀.obj K))) ≫
      P₁.map ((az.homEquiv _ _).symm
        (J₀.map (ax.unit.app K) ≫ j.app (Sx.obj K))) := by
  let b := (az.homEquiv _ _).symm
    (J₀.map (ax.unit.app K) ≫ j.app (Sx.obj K))
  apply (ay.homEquiv _ _).injective
  dsimp only [Functor.id_obj] at *
  rw [Equiv.apply_symm_apply, ay.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  change _ = (P₀.map (az.unit.app (J₀.obj K)) ≫ p.app _) ≫ Ry.map (P₁.map b)
  have hp := p.naturality b
  change P₀.map (Rz.map b) ≫ p.app _ = p.app _ ≫ Ry.map (P₁.map b) at hp
  dsimp only [Functor.id_obj] at hp
  rw [Category.assoc, ← hp]
  change _ = P₀.map (az.unit.app (J₀.obj K)) ≫ P₀.map (Rz.map b) ≫ _
  have hb : az.unit.app (J₀.obj K) ≫ Rz.map b =
      J₀.map (ax.unit.app K) ≫ j.app (Sx.obj K) :=
    az.homEquiv_apply _ _ b |>.symm.trans (Equiv.apply_symm_apply _ _)
  simpa only [P₀.map_comp, Category.assoc] using
    congrArg (fun t ↦ P₀.map t ≫ p.app (J₁.obj (Sx.obj K))) hb.symm

private def scalarTranspose
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁}
    (r : Rx ⋙ P₀ ⟶ P₁ ⋙ Ry) : P₀ ⋙ Sy ⟶ Sx ⋙ P₁ :=
  ((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _ r))

set_option backward.isDefEq.respectTransparency true in
private theorem scalarTranspose_app
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁}
    (r : Rx ⋙ P₀ ⟶ P₁ ⋙ Ry) (K : C₀) :
    (scalarTranspose ax ay r).app K =
      (ay.homEquiv _ _).symm (P₀.map (ax.unit.app K) ≫ r.app (Sx.obj K)) := by
  simp only [Functor.comp_obj, Functor.id_obj]
  apply (ay.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  simpa only [Adjunction.homEquiv_unit, scalarTranspose, TwoSquare.mk,
    Functor.id_obj, Functor.comp_obj] using
    (unit_mateEquiv_symm ax ay (TwoSquare.mk _ _ _ _ r) K).symm

private theorem scalar_transport_paste
    {Z₀ Z₁ D₀ D₁ : Type*}
    [Category Z₀] [Category Z₁] [Category D₀] [Category D₁]
    {P₀ : Z₀ ⥤ D₀} {P₁ : Z₁ ⥤ D₁}
    {Sz : Z₀ ⥤ Z₁} {Sy : D₀ ⥤ D₁}
    (α : P₀ ⋙ Sy ⟶ Sz ⋙ P₁)
    {U V : Z₀} {W T T' : Z₁} {D : D₀} {D' : D₁}
    (a : V ≅ U) (b : W ≅ T') (p : D ≅ P₀.obj V) (q : D' ≅ P₁.obj W)
    (o : Sz.obj U ⟶ T) (tx : T ⟶ T') (tz : Sz.obj V ⟶ W) (v : Sy.obj D ⟶ D')
    (ho : o ≫ tx = Sz.map a.inv ≫ tz ≫ b.hom)
    (hp : α.app V ≫ P₁.map tz = Sy.map p.inv ≫ v ≫ q.hom) :
    α.app U ≫ P₁.map o ≫ P₁.map tx =
      Sy.map (P₀.map a.inv ≫ p.inv) ≫ v ≫ q.hom ≫ P₁.map b.hom := by
  rw [← P₁.map_comp, ho, P₁.map_comp, P₁.map_comp]
  have hn := α.naturality a.inv
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [reassoc_of% hp]
  simp only [Functor.map_comp, Category.assoc]

private theorem intrinsic_scalar_transpose_paste
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).symm
      ((sfIntrinsicCompactSupport c A).map
          ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ)).unit.app K) ≫
        (sfCompactSupportRestriction c φ).hom.app
          ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K)) =
      ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).symm
        ((proEtaleConstantDerivedDirectImage c.g A).map
            ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := c.Z) φ)).unit.app
              ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K)) ≫
          (sfDerivedImageRestriction c.g φ).hom.app
            ((pbcDerivedExtend (proEtaleConstantRingMap (T := c.Z) φ)).obj
              ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K))) ≫
        (proEtaleConstantDerivedDirectImage c.g B).map
          (((pbcDerivedScalarAdjunction
            (proEtaleConstantRingMap (T := c.Z) φ)).homEquiv _ _).symm
              ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.map
                  ((pbcDerivedScalarAdjunction
                    (proEtaleConstantRingMap (T := X) φ)).unit.app K) ≫
                (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)).hom.app
                  ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K))) := by
  simpa only [sfIntrinsicCompactSupport, sfAmbientCompactSupportCandidate,
    sfCompactSupportRestriction, Functor.comp_map, Functor.comp_obj, Category.assoc,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    using scalar_transpose_paste
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := c.Z) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ))
      (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
      (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
      (proEtaleConstantDerivedDirectImage c.g A)
      (proEtaleConstantDerivedDirectImage c.g B)
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)).hom
      (sfDerivedImageRestriction c.g φ).hom K

private theorem exactPlus_obj
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory.Plus C) :
    (F.mapDerivedCategoryPlus.obj G).obj = F.mapDerivedCategory.obj G.obj := rfl

private theorem compactSiteIso_factors
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (compactSiteIso A c G).hom =
      (properSiteIso A c.g
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategoryPlus.obj G)).hom ≫
        (proEtaleConstantDerivedDirectImage c.g A).map
          ((openSiteIso A c.i).hom.app G.obj) := by
  let JA := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let NZ := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.Z
  let RP := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g
  let e := ProEtale.openImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  have hcomp : DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso JA NZ).inv.app G) =
      (Functor.mapDerivedCategoryCompIso JA NZ).hom.app G.obj := by
    have h : DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso JA NZ).app G) =
        (Functor.mapDerivedCategoryCompIso JA NZ).symm.app G.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app JA NZ G)
    exact congrArg Iso.inv h
  dsimp only [JA, NZ] at hcomp
  have he : DerivedCategory.Plus.ι.map
      ((ProEtale.properOpenSiteExtensionIso (ULift.{u + 1, u} A) c.i).hom.app G) =
      (Functor.mapDerivedCategorySquareIso e).hom.app G.obj := by
    simp only [ProEtale.properOpenSiteExtensionIso, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, hcomp,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app, e,
      ObjectProperty.ι_obj]
  have hn := RP.rightDerivedFunctorPlusCompatibility.hom.naturality
    ((ProEtale.properOpenSiteExtensionIso (ULift.{u + 1, u} A) c.i).hom.app G)
  dsimp only [RP, Functor.comp_map, Functor.comp_obj] at hn
  have hd := (sfIntrinsicDerivedDirectImageComparison c.g A).inv.naturality
    ((Functor.mapDerivedCategorySquareIso e).hom.app G.obj)
  dsimp only [e, Functor.comp_map, Functor.comp_obj] at hd
  simp only [compactSiteIso, compactRealizationIso, properSiteIso, openSiteIso,
    openRealizationIso, ProEtale.compactSupportSiteComparison,
    ProEtale.compactSupportSiteComparisonPlus,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    ProEtale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Functor.mapDerivedCategoryPlusCompatibility, Etale.rightDerivedLowerStarPlus,
    ObjectProperty.ι_obj, exactPlus_obj,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapIso_hom, asIso_hom, Functor.map_comp,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  simp only [sfIntrinsicCompactSupport, Functor.comp_map]
  try simp only [
    (Etale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor.map_id,
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.map_id,
    (sfIntrinsicDerivedEquivalence Y A).functor.map_id,
    (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor.map_id,
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.map_id,
    Category.id_comp]
  try simp only [← (sfIntrinsicDerivedEquivalence Y A).functor.map_comp_assoc]
  erw [hn, he]
  try simp only [(sfIntrinsicDerivedEquivalence Y A).functor.map_comp, Category.assoc]
  erw [reassoc_of% hd]
  erw [((proEtaleConstantDerivedDirectImage c.g A).mapIso
    ((intrinsicSiteFunctorIso A c.Z).app
      (JA.mapDerivedCategory.obj G.obj))).inv_hom_id_assoc]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [(proEtaleConstantDerivedDirectImage c.g A).map_comp,
    (sfIntrinsicDerivedEquivalence c.Z A).functor.map_comp, Category.assoc]

private theorem compactSiteIso_factors_iso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    compactSiteIso A c G =
      properSiteIso A c.g
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategoryPlus.obj G) ≪≫
        (proEtaleConstantDerivedDirectImage c.g A).mapIso ((openSiteIso A c.i).app G.obj) :=
  Iso.ext (compactSiteIso_factors A c G)

/-- Canonical transport identifies the scalar transpose, including its units and counits.
This is an equality of maps, rather than merely an isomorphism between their endpoints.

Source: Stacks Tags 0GL6, 09AL and 0D6J; the scalar-mate compatibility of
`etaleProEtale_scalar_mate`, followed by intrinsic realization.
(blueprint: lem-finite-compact-support-scalar-transport).

Proof: factor compact support as open extension followed by proper direct image.
Adjunction naturality factors its scalar transpose as the proper scalar transpose
followed by proper image of the open scalar transpose. For open extension the two
scalar composites are left adjoint to the same restriction composite. Its
unit-preserving uniqueness map is precisely openScalarIso; transporting the
sectionwise realization restriction square gives sfOpenRestriction. For proper
image, compute the restriction square and the realization square on a K-injective
B-complex and a K-injective resolution after restriction. The defining equations of
sfDerivedImageRestriction and sfIntrinsicDerivedDirectImageComparison identify both
paths with the same direct image of the resolution arrow, so cancellation of its
quasi-isomorphism gives equality. On the fixed-scalar sites apply
etaleProEtale_scalar_mate; boundedness of G and GB supplies its two bounded-below
hypotheses. The K-flat normalization of the inverse pullback mate identifies its
etale scalar pullback comparison with scalarPullbackIso. Whisker these identities,
then cancel the site and realization unit/counit isomorphisms. The resulting
composite is exactly intrinsicCompactScalarIsoOfOrigin, proving the equality.
The argument also covers zero rings, empty schemes and identity coefficient maps. -/
theorem intrinsicCompactScalarIsoOfOrigin_hom
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G.obj ≅
      GB.obj) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Y)).homEquiv _ _).symm
      ((sfIntrinsicCompactSupport c A).map
          ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app
            ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) ≫
        (sfCompactSupportRestriction c φ).hom.app
          ((pbcDerivedExtend (scalarRingMap φ X)).obj
            ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj))) =
      (intrinsicCompactScalarIsoOfOrigin φ c G GB eGB).hom := by
  let JA := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory
  let JB := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.i).mapDerivedCategory
  let H := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategoryPlus.obj G
  let HB := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.i).mapDerivedCategoryPlus.obj GB
  let eH : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) c.Z).obj
      H.obj ≅ HB.obj :=
    (Etale.FiniteCompactScalar.openScalarIso
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) c.i).app G.obj ≪≫ JB.mapIso eGB
  let IA := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let IB := (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
  let PA := proEtaleConstantDerivedDirectImage c.g A
  let PB := proEtaleConstantDerivedDirectImage c.g B
  let SZ := pbcDerivedExtend (scalarRingMap φ c.Z)
  let SY := pbcDerivedExtend (scalarRingMap φ Y)
  let K := (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj
  let az := pbcDerivedScalarAdjunction (scalarRingMap φ c.Z)
  let ay := pbcDerivedScalarAdjunction (scalarRingMap φ Y)
  let α := scalarTranspose az ay (sfDerivedImageRestriction c.g φ).hom
  let o := (az.homEquiv _ _).symm
    (IA.map ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app K) ≫
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)).hom.app
        ((pbcDerivedExtend (scalarRingMap φ X)).obj K))
  let a := (openSiteIso A c.i).app G.obj
  let b := (openSiteIso B c.i).app GB.obj
  let p := properSiteIso A c.g H
  let q := properSiteIso B c.g HB
  let tx := (siteScalarIso φ X).app G.obj ≪≫
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).mapIso eGB
  let tz := (siteScalarIso φ c.Z).app H.obj ≪≫
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison c.Z B).mapIso eH
  let v := (siteScalarIso φ Y).hom.app
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor.obj
        H.obj) ≫
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).map
      ((Etale.scalarMate (RingHom.ulift.{u + 1, u + 1, u, u} φ) c.g).app H.obj ≫
        (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g).rightDerivedFunctor.map
          eH.hom)
  have ho := openScalar_transport φ c.i G.obj GB.obj eGB
  have ho' : o ≫ IB.map tx.hom = SZ.map a.inv ≫ tz.hom ≫ b.hom := by
    simpa only [o, IB, tx, SZ, a, tz, b, eH, JB, H, IA, K, az,
      Iso.trans_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
      Functor.mapDerivedCategoryPlus, ObjectProperty.lift, Functor.comp_obj, Functor.id_obj,
      ObjectProperty.ι_obj] using ho
  have hp := properScalar_transport φ c.g H HB eH
  have hp' : α.app _ ≫ PB.map tz.hom = SY.map p.inv ≫ v ≫ q.hom := by
    simpa only [α, PB, tz, SY, p, v, q, az, ay, scalarTranspose_app,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using hp
  have ht := scalar_transport_paste α a b p q o (IB.map tx.hom) tz.hom v ho' hp'
  apply (cancel_mono ((sfIntrinsicCompactSupport c B).map tx.hom)).1
  rw [intrinsic_scalar_transpose_paste]
  simp only [Functor.id_obj]
  erw [← scalarTranspose_app]
  change (α.app (IA.obj K) ≫ PB.map o) ≫ PB.map (IB.map tx.hom) = _
  simp only [IA, K, PB, Functor.comp_obj] at ht ⊢
  erw [Category.assoc, ht]
  simp only [intrinsicCompactScalarIsoOfOrigin, compactSiteIso_factors_iso,
    Etale.FiniteCompactScalar.compactScalarIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
    p, q, a, b, v, eH, JB, tx, IB, H, HB, sfIntrinsicCompactSupport,
    Functor.comp_map, Functor.comp_obj]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  simp only [ObjectProperty.ι_obj, exactPlus_obj]
  erw [(ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).map_id,
    (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory.map_id, Category.comp_id]

end AlgebraicGeometry.Scheme.FiniteCompactScalar
