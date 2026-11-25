/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
/-! # Classical intrinsic coefficient module descent
Source: blueprint classical sheaves of modules, essential-image paragraph.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 20000] chartModuleSheafify chartWeakModuleSheafify

private def scalarFF {C : Type (w)} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type (w)) [CommRing A] :
    (coefficientModelFixedScalars J A).FullyFaithful where
  preimage {M N} f :=
    { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
        (J := J) (M₁ := M.val) (M₂ := N.val)
        (SheafOfModules.constantCoefficientUnit J A) N.isSheaf).symm
        { app := f.hom.app
          naturality g := by ext x; exact ConcreteCategory.congr_hom (f.hom.naturality g) x } }
  map_preimage f := by ext U x; rfl
  preimage_map f := by ext U x; rfl

private def fixedPresheaf {C : Type (w)} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type (w)) [CommRing A]
    (F : Sheaf J (ModuleCat.{w} A)) :
    PresheafOfModules.{w}
      ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj := F.obj.obj
  map f := F.obj.map f
  map_id U := by ext x; exact ConcreteCategory.congr_hom (F.obj.map_id U) x
  map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.obj.map_comp f g) x

private def extendFixed {C : Type (w)} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type (w)) [CommRing A]
    (F : Sheaf J (ModuleCat.{w} A)) :
    ConstantCompletion.Mod (ConstantCompletion.constant J A) :=
  PresheafOfModules.sheafify (SheafOfModules.constantCoefficientUnit J A)
    (M₀ := fixedPresheaf J A F)
    (A := (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).obj F) (𝟙 _)

private theorem extendFixed_smul {C : Type (w)} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type (w)) [CommRing A]
    (F : Sheaf J (ModuleCat.{w} A)) (U : Cᵒᵖ) (a : A)
    (x : F.obj.obj U) :
    (SheafOfModules.constantCoefficientUnit J A).app U a •
      (show (extendFixed J A F).val.obj U from x) = a • x := by
  exact (((PresheafOfModules.toSheafify (SheafOfModules.constantCoefficientUnit J A)
    (M₀ := fixedPresheaf J A F)
    (A := (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).obj F)
    (𝟙 _)).app U).hom.map_smul a x).symm

private def extendFixedIso {C : Type (w)} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type (w)) [CommRing A]
    (F : Sheaf J (ModuleCat.{w} A)) :
    (coefficientModelFixedScalars J A).obj (extendFixed J A F) ≅ F :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦
      { hom := ModuleCat.ofHom
          (X := ((coefficientModelFixedScalars J A).obj (extendFixed J A F)).obj.obj U)
          (Y := F.obj.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun a x ↦ extendFixed_smul J A F U a x }
        inv := ModuleCat.ofHom
          (X := F.obj.obj U)
          (Y := ((coefficientModelFixedScalars J A).obj (extendFixed J A F)).obj.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun a x ↦ (extendFixed_smul J A F U a x).symm }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl })
    (fun {_ _} _ ↦ by ext x; rfl))

private theorem scalarEquiv {C : Type (w)} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type (w)) [CommRing A] :
    (coefficientModelFixedScalars J A).IsEquivalence := by
  have := (scalarFF J A).full
  have := (scalarFF J A).faithful
  have : (coefficientModelFixedScalars J A).EssSurj :=
    ⟨fun F ↦ ⟨extendFixed J A F, ⟨extendFixedIso J A F⟩⟩⟩
  exact {}

private theorem comparisonRingMap_unit (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    SheafOfModules.constantCoefficientUnit
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ≫
      (constructibleComparisonRingMap.{u, v} X A).hom =
        Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
          (SheafOfModules.constantCoefficientUnit
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) := by
  have h := ((sheafificationAdjunction
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    CommRingCat.{max v (u + 1)}).homEquiv
      ((Functor.const (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ).obj
        (CommRingCat.of A))
      ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
        CommRingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) |>.obj
          (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))).apply_symm_apply
      (Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
        (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
          ((Functor.const _).obj (CommRingCat.of A))))
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})) h

private def comparisonFixedRight (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    SheafOfModules.pushforward (constructibleComparisonRingMap.{u, v} X A) ⋙
        coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ⋙
        (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have h (U : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ) (a : A) :
      (constructibleComparisonRingMap.{u, v} X A).hom.app U
          ((SheafOfModules.constantCoefficientUnit
            (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).app U a) =
        (SheafOfModules.constantCoefficientUnit
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).app
            ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) a :=
    ConcreteCategory.congr_hom (congr_app (comparisonRingMap_unit.{u, v} X A) U) a
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)
    · let P := ((SheafOfModules.pushforward
        (constructibleComparisonRingMap.{u, v} X A) ⋙
          coefficientModelFixedScalars
            (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).obj M).obj.obj U
      let Q := ((coefficientModelFixedScalars
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ⋙
        (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj M).obj.obj U
      exact
        { hom := ModuleCat.ofHom (X := P) (Y := Q)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := by
                intro a x
                change (constructibleComparisonRingMap.{u, v} X A).hom.app U
                    ((SheafOfModules.constantCoefficientUnit
                      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).app U a) •
                      (show M.val.obj
                        ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) from x) =
                  (SheafOfModules.constantCoefficientUnit
                    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).app
                      ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) a •
                      (show M.val.obj
                        ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) from x)
                rw [h U a] }
          inv := ModuleCat.ofHom (X := Q) (Y := P)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := by
                intro a x
                change (SheafOfModules.constantCoefficientUnit
                    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).app
                      ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) a •
                        (show M.val.obj
                          ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) from x) =
                  (constructibleComparisonRingMap.{u, v} X A).hom.app U
                    ((SheafOfModules.constantCoefficientUnit
                      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).app U a) •
                      (show M.val.obj
                        ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) from x)
                rw [h U a] }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intro U V f
      ext x
      rfl
  · intro M N f
    ext U x
    rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def comparisonFixedLeft (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    constructibleComparisonPullback.{u, v} X A ⋙
        coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have := scalarEquiv (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalarEquiv (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let eE := (coefficientModelFixedScalars
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).asEquivalence
  let eP := (coefficientModelFixedScalars
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).asEquivalence
  let R := SheafOfModules.pushforward (constructibleComparisonRingMap.{u, v} X A)
  let S := (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  let adj₁ := (SheafOfModules.pullbackPushforwardAdjunction
    (constructibleComparisonRingMap.{u, v} X A)).comp eP.toAdjunction
  let adj₂ := eE.toAdjunction.comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X))
  let r : eP.inverse ⋙ R ≅ S ⋙ eE.inverse :=
    Functor.isoWhiskerLeft (eP.inverse ⋙ R) eE.unitIso ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eP.inverse (comparisonFixedRight.{u, v} X A)) eE.inverse ≪≫
      Functor.isoWhiskerRight eP.counitIso (S ⋙ eE.inverse)
  exact adj₁.leftAdjointUniq (adj₂.ofNatIsoRight r.symm)

private theorem isoAtColimit {C J D : Type*} [Category* C] [Category* J]
    [Category D] {F G : Cᵒᵖ ⥤ D} (a : F ⟶ G) {K : J ⥤ C} (c : Cone K)
    (hF : IsColimit (F.mapCocone c.op)) (hG : IsColimit (G.mapCocone c.op))
    [∀ i, IsIso (a.app (op (K.obj i)))] : IsIso (a.app (op c.pt)) := by
  let e : K.op ⋙ F ≅ K.op ⋙ G := NatIso.ofComponents
    (fun i ↦ asIso (a.app (op (K.obj i.unop))))
    (fun f ↦ a.naturality (K.map f.unop).op)
  let h := (IsColimit.precomposeHomEquiv e (G.mapCocone c.op)).2 hG
  have heq : a.app (op c.pt) = (hF.coconePointUniqueUpToIso h).hom := by
    apply hF.hom_ext
    intro i
    change F.map (c.π.app i.unop).op ≫ a.app (op c.pt) = _
    simp only [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact a.naturality (c.π.app i.unop).op
  rw [heq]
  infer_instance

private theorem basisPresentation (X : Scheme.{u}) (U : X.AffineProEt) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsCofiltered I)
      (P : AffinePresentation X I), P.cone.pt = (Scheme.AffineProEt.toProEt X).obj U := by
  have h := U.prop
  change MorphismProperty.pro.{u}
    (@Etale ⊓ MorphismProperty.ofObjectProperty (IsAffine ·) ⊤) U.hom at h
  have hlarge : MorphismProperty.pro.{u + 1}
      (@Etale ⊓ MorphismProperty.ofObjectProperty (IsAffine ·) ⊤) U.hom :=
    MorphismProperty.pro_of_univLE.{u, u + 1} _ h
  obtain ⟨I, _, _, D, t, s, hs, hts⟩ := hlarge
  have haff (i : I) : IsAffine (D.obj i) := (hts i).1.2.1
  have het (i : I) : Etale (t.app i) := (hts i).1.1
  let E : I ⥤ X.ProEt := MorphismProperty.Over.lift' D t
    (fun i ↦ inferInstanceAs (WeaklyEtale (t.app i))) (fun _ ↦ trivial)
  let c : Cone E :=
    { pt := (Scheme.AffineProEt.toProEt X).obj U
      π :=
        { app i := MorphismProperty.Over.homMk (s.app i) (hts i).2
          naturality {i j} a := by
            apply MorphismProperty.Over.Hom.ext
            change s.app j = s.app i ≫ D.map a
            simpa using s.naturality a } }
  refine ⟨I, inferInstance, inferInstance,
    { diagram := E
      affine := haff
      etale := het
      cone := c
      affineVertex := U.prop.isAffine
      isLimit := ?_ }, rfl⟩
  have : IsConnected I := IsCofiltered.isConnected I
  exact isLimitOfReflects (Over.forget X) hs

private theorem fixedCounitStages (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) (i : I) :
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    IsIso ((adj.counit.app F).hom.app (op (AsSmall.up.obj (P.diagram.obj i)))) := by
  let B := Scheme.smallModelComparisonInclusion.{u, v} X
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let M := ModuleCat.{max v (u + 1)} A
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B M J K
  let G := (B.sheafPushforwardContinuous M J K).obj F
  let W : X.Etale := @Scheme.Etale.mk _ _ (P.diagram.obj i).hom (P.etale i)
  let V := op (AsSmall.up.obj W)
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤
      X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  have : B.op.Full := inferInstance
  have : B.op.Faithful := inferInstance
  have hu : (adj.unit.app G).hom = B.op.lanUnit.app G.obj ≫
      Functor.whiskerLeft B.op (toSheafify K (B.op.lan.obj G.obj)) := by
    change (sheafToPresheaf J M).map (adj.unit.app G) = _
    dsimp only [adj]
    rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.map_restrictFullyFaithful_unit_app]
    simp
  have : B.op.HasPointwiseLeftKanExtension G.obj := by infer_instance
  have hη := (coefficientComparison_presentation_toSheafify_isIso X A G P).2 i
  have hunit : IsIso ((adj.unit.app G).hom.app V) := by
    rw [hu, NatTrans.comp_app]
    have : IsIso ((toSheafify K (B.op.lan.obj G.obj)).app (B.op.obj V)) := hη
    have : IsIso ((B.op.lanUnit.app G.obj).app V) := by infer_instance
    change IsIso ((B.op.lanUnit.app G.obj).app V ≫
      (toSheafify K (B.op.lan.obj G.obj)).app (B.op.obj V))
    infer_instance
  have heq := congrArg (fun f ↦ f.hom.app V) (adj.right_triangle_components F)
  change (adj.unit.app G).hom.app V ≫ (adj.counit.app F).hom.app
    (op (AsSmall.up.obj (P.diagram.obj i))) = 𝟙 _ at heq
  apply (isIso_comp_left_iff ((adj.unit.app G).hom.app V) _).mp
  rw [heq]
  infer_instance

private theorem fixedOrigin (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hF : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I),
      IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          F.obj))) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage F := by
  let B := Scheme.smallModelComparisonInclusion.{u, v} X
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let M := ModuleCat.{max v (u + 1)} A
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B M J K
  let G := (B.sheafPushforwardContinuous M J K).obj F
  let Q := (AsSmall.up : X.ProEt ⥤
    Scheme.coefficientProEtaleSiteModel.{u, v} X).sheafPushforwardContinuous M
      (Scheme.ProEt.topology X) K
  have : (AsSmall.up : X.ProEt ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  have hb : IsIso (Q.map (adj.counit.app F)) := by
    refine Functor.IsCoverDense.iso_of_restrict_iso
      (G := Scheme.AffineProEt.toProEt X) (Q.map (adj.counit.app F)) ?_
    change IsIso ((Scheme.AffineProEt.toProEt X).op.whiskerLeft
      (Functor.whiskerLeft AsSmall.up.op (adj.counit.app F).hom))
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    obtain ⟨I, _, _, P, hP⟩ := basisPresentation X U.unop
    change IsIso ((adj.counit.app F).hom.app
      (op (AsSmall.up.obj ((Scheme.AffineProEt.toProEt X).obj U.unop))))
    rw [← hP]
    let a := Functor.whiskerLeft
      (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op
      (adj.counit.app F).hom
    have (i : I) : IsIso (a.app (op (P.diagram.obj i))) := fixedCounitStages X A F P i
    obtain ⟨hs⟩ := coefficientFixedComparison_isColimit X A G P
    have ht : IsColimit (sectionCocone P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          F.obj)) := by
      have : IsIso ((colimit.isColimit _).desc (sectionCocone P
          ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
            F.obj))) := hF P
      exact (colimit.isColimit _).ofPointIso
    exact isoAtColimit a P.cone hs ht
  have hc : IsIso (adj.counit.app F) :=
    Functor.IsCoverDense.iso_of_restrict_iso
      (G := (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X))
      (adj.counit.app F)
      (((sheafToPresheaf (Scheme.ProEt.topology X) M).mapIso
        (asIso (Q.map (adj.counit.app F)))).isIso_hom)
  exact ⟨G, ⟨asIso (adj.counit.app F)⟩⟩

/-- A module with invertible affine continuity maps has an etale module antecedent.
There is no constructibility or Noetherianity assumption.
Source: blueprint theorem-classical-sheaves-essential-image--1, essential-image paragraph;
Bhatt--Scholze, The pro-etale topology for schemes, Lemma 5.1.2
(auxiliary; not a blueprint node).

Proof: the constant-scalar equivalence identifies intrinsic constant-ring modules
with sheaves of modules over the discrete coefficient ring. Transport the module
and its continuity maps through the AsSmall site equivalence. Forgetting to sets
preserves the filtered colimits in the continuity maps and reflects isomorphisms,
so its underlying set sheaf is classical. The classical-sheaf counit criterion
makes its set comparison counit invertible. Addition and every scalar action are
natural, and the constant-section equation identifies this with the forgotten
module counit. Forgetting modules reflects isomorphisms sectionwise. The intrinsic
module counit is therefore invertible, and its source is the inverse image of the
direct-image module, furnishing the desired antecedent. This proof also applies
to the zero module, zero ring and empty scheme. -/
theorem coefficientClassicalModule_origin (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
    (hF : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I),
      IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          ((coefficientModelFixedScalars _ A).obj F).obj))) :
    ∃ G, Nonempty ((constructibleComparisonPullback X A).obj G ≅ F) := by
  have := scalarEquiv (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalarEquiv (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let E := coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  let P := coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  obtain ⟨G, ⟨e⟩⟩ := fixedOrigin X A (P.obj F) hF
  refine ⟨E.objPreimage G, ⟨P.preimageIso ?_⟩⟩
  exact (comparisonFixedLeft X A).app (E.objPreimage G) ≪≫
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).mapIso (E.objObjPreimageIso G) ≪≫ e
end AlgebraicGeometry.ProEtale
