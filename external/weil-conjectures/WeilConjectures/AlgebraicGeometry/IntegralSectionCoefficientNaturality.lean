/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # The coefficient equation for the integral section comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage

private theorem inverseImageUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D]
    (G : Sheaf (Scheme.ProEt.topology Y) D) :
    ((Scheme.proEtaleSheafAdjunction f D).unit.app G).hom =
      (Scheme.proEtaleBaseChange f).op.leftKanExtensionUnit G.obj ≫
        Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
          (toSheafify (Scheme.ProEt.topology X)
            ((Scheme.proEtaleBaseChange f).op.leftKanExtension G.obj)) := by
  let U : Y.ProEt ⥤ X.ProEt := Scheme.proEtaleBaseChange f
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction D).comp (sheafificationAdjunction (Scheme.ProEt.topology X) D))
    (fullyFaithfulSheafToPresheaf (Scheme.ProEt.topology Y) D)
    (Functor.FullyFaithful.id _)
    (L := Scheme.proEtaleSheafInverseImage f D)
    (R := Scheme.proEtaleSheafDirectImage f D) (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app, Functor.lanAdjunction_unit] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  exact h

private theorem commRingAbPreservesSheafification (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
  let G := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : PreservesLimitsOfSize.{u + 1, u + 1} G := inferInstance
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} G := inferInstance
  let J := Scheme.ProEt.topology X
  have : PreservesLimitsOfSize.{u + 1, u + 1} (forget CommRingCat.{u + 1}) :=
    inferInstance
  have : PreservesLimitsOfSize.{u + 1, u + 1} (forget Ab.{u + 1}) := inferInstance
  have (V : X.ProEt) : HasColimitsOfShape (J.Cover V)ᵒᵖ CommRingCat.{u + 1} :=
    inferInstance
  have (V : X.ProEt) : HasColimitsOfShape (J.Cover V)ᵒᵖ Ab.{u + 1} := inferInstance
  have (V : X.ProEt) : PreservesColimitsOfShape (J.Cover V)ᵒᵖ G := inferInstance
  have (V : X.ProEt) : PreservesColimitsOfShape (J.Cover V)ᵒᵖ
      (forget CommRingCat.{u + 1}) := inferInstance
  have (V : X.ProEt) : PreservesColimitsOfShape (J.Cover V)ᵒᵖ
      (forget Ab.{u + 1}) := inferInstance
  have (V : X.ProEt) (W : J.Cover V) (P : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1}) :
      PreservesLimit (W.index P).multicospan G := inferInstance
  change J.PreservesSheafification G
  rw [GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
    J G (plusPlusAdjunction J CommRingCat.{u + 1}) (plusPlusAdjunction J Ab.{u + 1})]
  infer_instance

private def commRingAbPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (Scheme.ProEt.topology X) Ab.{u + 1}] :
    Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) ⋙
        Scheme.proEtaleSheafInverseImage f Ab.{u + 1} := by
  let U : Y.ProEt ⥤ X.ProEt := Scheme.proEtaleBaseChange f
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let G := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have (P : Y.ProEtᵒᵖ ⥤ CommRingCat.{u + 1}) :
      G.PreservesPointwiseLeftKanExtension P U.op := fun W ↦ by
    have : IsFiltered (CostructuredArrow U.op W) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
    have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
      have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
      have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
      infer_instance
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W
  have (P : Y.ProEtᵒᵖ ⥤ CommRingCat.{u + 1}) : U.op.HasLeftKanExtension P :=
    inferInstance
  have (P : Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) : U.op.HasLeftKanExtension P :=
    inferInstance
  have := commRingAbPreservesSheafification X
  let eLan := G.lanCompIsoOfPreserves U.op
  let eSh := sheafComposeNatIso (Scheme.ProEt.topology X) G
    (sheafificationAdjunction _ CommRingCat.{u + 1})
    (sheafificationAdjunction _ Ab.{u + 1})
  exact Functor.isoWhiskerLeft
      (sheafToPresheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1} ⋙ U.op.lan) eSh.symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
      (Functor.isoWhiskerRight eLan (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}))

private theorem commRingAbPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (Scheme.ProEt.topology X) Ab.{u + 1}]
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    let U : Y.ProEt ⥤ X.ProEt := Scheme.proEtaleBaseChange f
    ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).unit.app
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)).hom ≫
        Functor.whiskerLeft U.op ((commRingAbPullback f).inv.app R).hom =
      Functor.whiskerRight
        ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
  let U : Y.ProEt ⥤ X.ProEt := Scheme.proEtaleBaseChange f
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let G := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have (P : Y.ProEtᵒᵖ ⥤ CommRingCat.{u + 1}) :
      G.PreservesPointwiseLeftKanExtension P U.op := fun W ↦ by
    have : IsFiltered (CostructuredArrow U.op W) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
    have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
      have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
      have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
      infer_instance
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W
  dsimp only
  dsimp only [Scheme.proEtaleSheafInverseImage, Scheme.proEtaleSheafDirectImage,
    Functor.sheafPullbackConstruction.sheafPullback, lowerStar, Functor.comp_obj]
  erw [inverseImageUnit]
  unfold commRingAbPullback
  erw [Iso.trans_inv]
  dsimp only [NatTrans.comp_app]
  erw [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv]
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Iso.symm_inv]
  erw [ObjectProperty.FullSubcategory.comp_hom]
  erw [Category.assoc, ← Functor.whiskerLeft_comp]
  erw [← Category.assoc, ← toSheafify_naturality]
  have := commRingAbPreservesSheafification X
  let e := G.leftKanExtensionCompIsoOfPreserves R.obj U.op
  let sh := (sheafComposeNatIso (Scheme.ProEt.topology X) G
    (sheafificationAdjunction _ CommRingCat.{u + 1})
    (sheafificationAdjunction _ Ab.{u + 1})).hom.app (U.op.leftKanExtension R.obj)
  change (U.op.leftKanExtensionUnit (R.obj ⋙ G) ≫
      Functor.whiskerLeft U.op (e.inv ≫ toSheafify (Scheme.ProEt.topology X)
        (U.op.leftKanExtension R.obj ⋙ G))) ≫ Functor.whiskerLeft U.op sh.hom = _
  have hfac := Functor.leftKanExtensionCompIsoOfPreserves_inv_fac G R.obj U.op
  have hs := sheafComposeNatTrans_fac (Scheme.ProEt.topology X) G
    (sheafificationAdjunction _ CommRingCat.{u + 1})
    (sheafificationAdjunction _ Ab.{u + 1}) (U.op.leftKanExtension R.obj)
  trans (U.op.leftKanExtensionUnit (R.obj ⋙ G) ≫ Functor.whiskerLeft U.op e.inv) ≫
      Functor.whiskerLeft U.op
        (toSheafify (Scheme.ProEt.topology X) (U.op.leftKanExtension R.obj ⋙ G) ≫
          sh.hom)
  · simp only [Functor.whiskerLeft_comp, Category.assoc]
  · rw [hfac]
    erw [hs]
    erw [inverseImageUnit f CommRingCat.{u + 1} R]
    ext W x
    rfl

private theorem reconstructedCoefficientPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) (condensedRingObj Λ Y)
    let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)
    ∃ c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S,
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R ≫
            (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map c.hom) =
        InternalModuleOperations.coefficientMap Λ f := by
  let : HasWeakSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    (GrothendieckTopology.hasSheafify_proEtTopology Ab.{u + 1} X).isRightAdjoint
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) (condensedRingObj Λ Y)
  let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let FY := sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let FX := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})
  let AY := sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})
  let φ : R ⟶ (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S :=
    FY.preimage (InternalModuleOperations.coefficientMap Λ f)
  have hφ : AY.map φ = condensedPushforwardHom Λ f := by
    ext V r
    have h := congrArg (fun t ↦ (t.hom.app V).hom r)
      (FY.map_preimage (X := R)
        (Y := (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S)
        (InternalModuleOperations.coefficientMap Λ f))
    exact h.trans (InternalModuleOperations.coefficientMap_apply Λ f V r)
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let c := (adj.homEquiv R S).symm φ
  have hc : adj.unit.app R ≫
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map c = φ :=
    (adj.homEquiv R S).apply_symm_apply φ
  have hab : (commRingAbPullback f).inv.app R ≫ FX.map c =
      condensedPullbackHom Λ f := by
    apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
      (condensedRingObj Λ Y) (condensedRingObj Λ X)).injective
    change (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _ ≫
        (f)_*[Ab.{u + 1}].map ((commRingAbPullback f).inv.app R ≫ FX.map c) =
      condensedPushforwardHom Λ f
    erw [CategoryTheory.Functor.map_comp, ← Category.assoc]
    have hu := commRingAbPullback_unit f R
    have hu' : (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _ ≫
        (f)_*[Ab.{u + 1}].map ((commRingAbPullback f).inv.app R) =
      AY.map (adj.unit.app R) := by
      exact Sheaf.hom_ext hu
    erw [hu']
    change AY.map (adj.unit.app R ≫
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map c) = _
    rw [hc, hφ]
  have : IsIso ((commRingAbPullback f).inv.app R ≫ FX.map c) := by
    rw [hab]
    exact isIso_condensedPullbackHom Λ f
  have : IsIso (FX.map c) := IsIso.of_isIso_comp_left ((commRingAbPullback f).inv.app R) _
  have : IsIso c := isIso_of_reflects_iso c FX
  refine ⟨asIso c, ?_⟩
  change FY.map (adj.unit.app R ≫
    (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map c) = _
  rw [hc]
  exact FY.map_preimage _

/-- Compare the detailed completed ring directly with the reconstructed internal ring.
Both factors are the prescribed, projection-normalized comparisons.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(auxiliary; not a blueprint node). -/
def integralDetailedSectionRingComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (Scheme.adicLisseForget X).obj
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) ≅
      InternalModuleOperations.ring (DerivedNakayama.integerRing l E) X :=
  Scheme.integralDetailedCoefficientComparison X l E ≪≫
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (integralSectionRingIso l E X).symm

/-- The completed coefficient comparison is compatible with the actual inverse-image
unit. This assertion concerns rings only; it makes no assertion about module functors
or local isomorphism classes.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the coefficient
square in the integral constructibility comparison; Stacks, Tags 00YV and 03D2.
(auxiliary; not a blueprint node).

Proof: forget commutative ring sheaves to ring sheaves and lift the fixed source
comparison through this fully faithful functor. For the reconstructed coefficient
rings, lift the internal direct-image coefficient map in the same way, then take
its adjunct in commutative ring sheaves. Forgetting this adjunct to abelian sheaves
identifies it with the point-pullback comparison: forgetting commutative rings to
abelian groups commutes with the filtered Kan extension and sheafification used
in inverse image, compatibly with the adjunction units. The point-pullback
comparison is an isomorphism, so reflection of isomorphisms makes the ring adjunct
an isomorphism. Compose it with inverse image of the fixed source comparison.
Naturality of the unit proves the displayed square. The adjunction and faithful
forgetful functor give uniqueness. No normalization on the target scheme is
required; the target ring is the reconstructed internal coefficient ring. -/
theorem integralSectionCoefficientNaturality (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) :
    let R := Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)
    let P := (Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R
    let F := Scheme.proEtaleBaseChange g
    let J := Scheme.ProEt.topology X
    let K := Scheme.ProEt.topology S
    let B := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj P
    let a : (Scheme.adicLisseForget X).obj R ⟶
        (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj B :=
      ⟨Functor.whiskerRight
        ((Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    ∃! c : B ≅ InternalModuleOperations.ring (DerivedNakayama.integerRing l E) S,
      (integralDetailedSectionRingComparison l E X).hom ≫
          InternalModuleOperations.coefficientMap (DerivedNakayama.integerRing l E) g =
        a ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map c.hom := by
  let Λ := DerivedNakayama.integerRing l E
  let R := Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)
  let RX := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let RS := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology S) (condensedRingObj Λ S)
  let FX := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let FS := sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let P := Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}
  let adj := Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let d : R ≅ RX := FX.preimageIso (integralDetailedSectionRingComparison l E X)
  have hd : FX.map d.hom = (integralDetailedSectionRingComparison l E X).hom :=
    FX.map_preimage _
  obtain ⟨c0, hc0⟩ := reconstructedCoefficientPullback Λ g
  let c := (Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso d ≪≫ c0
  have hsquare : d.hom ≫ adj.unit.app RX ≫ P.map c0.hom =
      adj.unit.app R ≫ P.map c.hom := by
    dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
    have hn := adj.unit.naturality d.hom
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, Functor.map_comp]
    rfl
  have he : (integralDetailedSectionRingComparison l E X).hom ≫
        InternalModuleOperations.coefficientMap Λ g =
      FX.map (adj.unit.app R ≫ P.map c.hom) := by
    calc
      _ = FX.map (d.hom ≫ adj.unit.app RX ≫ P.map c0.hom) := by
        rw [FX.map_comp, FX.map_comp, hd, ← hc0, FX.map_comp]
        rfl
      _ = _ := congrArg (fun k ↦ FX.map k) hsquare
  refine ⟨FS.mapIso c, ?_, ?_⟩
  · exact he
  · intro e he'
    apply Iso.ext
    have h : FS.preimage e.hom = c.hom := by
      apply (adj.homEquiv R RS).injective
      apply FX.map_injective
      change FX.map (adj.unit.app R ≫ P.map (FS.preimage e.hom)) =
        FX.map (adj.unit.app R ≫ P.map c.hom)
      rw [FX.map_comp, FX.map_comp]
      change _ ≫ ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology S)).map
            (FS.map (FS.preimage e.hom)) = _
      rw [FS.map_preimage]
      exact he'.symm.trans he
    exact (FS.map_preimage e.hom).symm.trans (congrArg (fun k ↦ FS.map k) h)

end AlgebraicGeometry.ProEtale
