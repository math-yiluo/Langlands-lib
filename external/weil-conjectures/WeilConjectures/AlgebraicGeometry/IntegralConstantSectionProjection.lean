/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientModel
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionRing
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares
import WeilConjectures.SixFunctors.ProEtale.IntegralSectionProjectionNormalization

/-! # Finite projections of the canonical integral section comparison

Source: Stacks Tags 099L and 099M, integral-models proof (1)--(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local instance] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify

/-- The explicit universe instance for ordinary coefficient comparisons.
Source: coefficient-site sheafification
(auxiliary; not a blueprint node). -/
local instance projectionAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

attribute [local instance] WeilConjectures.instEssentiallySmallProEt_weilConjectures

attribute [local irreducible] upperStarFromPoint IntegralConstantModel.pointComparison
  completedSectionIso
  integralSectionRingIso WeilConjectures.purCoefficientIso Scheme.pbcCompletedComparison

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- A ring comparison is normalized by its specified map on constant additive sections.
Source: Stacks Tags 03CY and 00YV (auxiliary; not a blueprint node).
-/
def DiscreteSectionRingNormalized (X : Scheme.{u}) (A : Type u) [CommRing A]
    (d : Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X)) : Prop :=
  ∀ (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A),
    d.hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of.{u + 1} (ULift.{u + 1} A)))).app U a) =
      (discreteCoefficientAbelianIso X A).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)))).app U a)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- The ordinary normalized integral and first-residue ring comparisons, with the
projection equations required for their canonical coefficient actions.
Source: Stacks Tags 099L and 099M (auxiliary; not a blueprint node).
-/
structure IntegralSectionComparisons (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) where
  integers : Scheme.adicLisseConstantRing X (IntegralConstantCompletion.integers l E) ≅
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X)
  residue : Scheme.adicLisseConstantRing X
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) ≅
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (condensedRingObj (discreteObj (Padic.coefficientExtensionRing l E 1)) X)
  integers_normalized :
    DiscreteSectionRingNormalized X (Padic.coefficientExtensionIntegers l E) integers
  residue_normalized :
    DiscreteSectionRingNormalized X (Padic.coefficientExtensionRing l E 1) residue
  reduction_naturality :
    integers.hom ≫ sectionMap X ((upperStarFromPoint X).map (discreteMap
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)))) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom.{u + 1} (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
            ULift.ringEquiv.toRingHom))) ≫ residue.hom
  projection (n : ℕ) :
    integers.hom ≫ sectionMap X (scalarMap l E X) ≫ (completedSectionIso l E X).inv ≫
        limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)) (op n) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom.{u + 1} (Ideal.Quotient.mk
          (IntegralConstantCompletion.ideal l E ^ (n + 1))))

private theorem topologyAb_eq (B : Type u) [Ring B]
    (t₁ t₂ : TopologicalSpace B) (ht : t₁ = t₂)
    (h₁ : @IsTopologicalRing B t₁ _) (h₂ : @IsTopologicalRing B t₂ _) :
    let V := sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})
    eqToHom (congrArg V.obj (continuousRingSheaf_topology_eq B t₁ t₂ ht h₁ h₂)) =
      V.map (IntegralPresentation.continuousRingTopologyIso B t₁ t₂ ht h₁ h₂).hom := by
  subst t₂
  rfl

private theorem monHom_eqToHom
    {C : Type*} [Category C] [MonoidalCategory C]
    {M N : Mon C} (h : M = N) :
    (eqToIso h).hom.hom = eqToHom (congrArg (fun P : Mon C ↦ P.X) h) := by
  subst N
  rfl

private theorem pointComparison_forget (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (IntegralConstantModel.pointComparison l E).hom.hom =
      eqToHom (congrArg
        (fun R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ↦ R.X)
        (IntegralConstantModel.pointEquality l E)) := by
  unfold IntegralConstantModel.pointComparison
  exact monHom_eqToHom (IntegralConstantModel.pointEquality l E)

private theorem pointComparison_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (IntegralConstantModel.pointComparison l E).hom.hom =
      (IntegralPresentation.integerPointIso l E).hom := by
  let B := Padic.coefficientExtensionIntegers l E
  let t₁ := TopologicalSpace.induced (fun x : B ↦ (x : E))
    ((Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace
      |>.toUniformSpace.toTopologicalSpace)
  let t₂ := TopologicalSpace.induced (fun x : B ↦ (x : E))
    (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have ht : t₁ = t₂ := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : B ↦ (x : E)) t)
      (DerivedNakayama.coefficientTopology l E).symm
  let h₁ : @IsTopologicalRing B t₁ _ := by
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    infer_instance
  let h₂ : @IsTopologicalRing B t₂ _ := by
    letI := spectralNorm.normedField (Padic l) E
    infer_instance
  let V := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  rw [pointComparison_forget]
  exact topologyAb_eq B t₁ t₂ ht h₁ h₂

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem completed_projection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom ≫
        (WeilConjectures.purCoefficientIso l E X).hom ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n =
      limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)) (op n) ≫
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (Scheme.integralCoefficientULift l E n).toCommRingCatIso.hom := by
  let F := Scheme.adicLisseForget X
  let c := Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)
  let t := Scheme.pbcLevelConstantComparison X (Scheme.pbcIntegralDatum l E) n
  have he : F.map (WeilConjectures.purCoefficientIso l E X).hom =
      (Scheme.integralDetailedCoefficientComparison X l E).hom := by
    simpa only [WeilConjectures.purCoefficientIso, Functor.mapIso_hom] using
      congrArg Iso.hom (WeilConjectures.purCoefficientIso_existsUnique l E X).exists.choose_spec
  have hc : c.hom ≫ Scheme.pbcAdicProjection X (Scheme.pbcIntegralDatum l E) n =
      limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)) (op n) ≫
        t.hom := by
    simpa only [c, t, Scheme.pbcCompletedComparison, Scheme.pbcAdicProjection,
      Scheme.pbcConstantSystemComparison, NatIso.ofComponents_hom_app,
      Scheme.adicLisseCompletedRing, Scheme.pbcAdicRings, Scheme.pbcIntegralDatum,
      Scheme.pbcUniformizer, IntegralConstantCompletion.ideal] using
      HasLimit.isoOfNatIso_hom_π
        (Scheme.pbcConstantSystemComparison X (Scheme.pbcIntegralDatum l E)) (op n)
  apply F.map_injective
  simp only [Functor.map_comp]
  change F.map c.hom ≫ (F.mapIso (WeilConjectures.purCoefficientIso l E X)).hom ≫
    limit.π (WeilConjectures.integralCoefficientSheafSystem l E X) (op n) = _
  simp only [Functor.mapIso_hom]
  erw [he, (Scheme.integralDetailedCoefficientComparison_exists X l E).exists.choose_spec n]
  rw [← F.map_comp_assoc, hc]
  simp only [Functor.map_comp, Category.assoc]
  change _ ≫ F.map t.hom ≫ F.map (t.inv ≫ _) = _
  rw [← F.map_comp, Iso.hom_inv_id_assoc]
  rfl

private theorem pointComparison_inv_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (IntegralConstantModel.pointComparison l E).inv.hom =
      (IntegralPresentation.integerPointIso l E).inv := by
  apply (cancel_epi (IntegralConstantModel.pointComparison l E).hom.hom).mp
  calc
    (IntegralConstantModel.pointComparison l E).hom.hom ≫
        (IntegralConstantModel.pointComparison l E).inv.hom = 𝟙 _ :=
      congrArg (fun f ↦ f.hom) (IntegralConstantModel.pointComparison l E).hom_inv_id
    _ = _ := by rw [pointComparison_eq, Iso.hom_inv_id]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem canonicalAbelianMap_scalar_natural
    (B C : Type u) [CommRing B] [CommRing C]
    [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalRing B] [IsTopologicalRing C]
    (f : ULift.{u + 1} B →+ ULift.{u + 1} C)
    (g : FiniteDiscreteOrdinary.coefficient B ⟶ FiniteDiscreteOrdinary.coefficient C)
    (h : FiniteDiscreteOrdinary.pointConstants B ≫ g.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom.{u + 1} f) ≫
        FiniteDiscreteOrdinary.pointConstants C) (X : Scheme.{u}) :
    letI : EssentiallySmall.{u + 1} X.ProEt :=
      WeilConjectures.instEssentiallySmallProEt_weilConjectures X
    letI : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
    letI : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
    FiniteDiscreteOrdinary.canonicalAbelianMap B X ≫ (upperStarFromPoint X).map g =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom.{u + 1} f) ≫ FiniteDiscreteOrdinary.canonicalAbelianMap C X := by
  let J := coherentTopology Profinite.{u}
  let eB := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (FiniteDiscreteOrdinary.coefficient B)).symm (FiniteDiscreteOrdinary.pointConstants B)
  let eC := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (FiniteDiscreteOrdinary.coefficient C)).symm (FiniteDiscreteOrdinary.pointConstants C)
  have hB : toSheafify J ((Functor.const _).obj (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} B))) ≫
      eB.hom = FiniteDiscreteOrdinary.pointConstants B :=
    ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hC : toSheafify J ((Functor.const _).obj (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} C))) ≫
      eC.hom = FiniteDiscreteOrdinary.pointConstants C :=
    ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  have he : eB ≫ g = (constantSheaf J Ab.{u + 1}).map
      (AddCommGrpCat.ofHom.{u + 1} f) ≫ eC := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (FiniteDiscreteOrdinary.coefficient C).property
    change _ ≫ (eB.hom ≫ g.hom) = _ ≫ (_ ≫ eC.hom)
    change (toSheafify J _ ≫ eB.hom) ≫ g.hom =
      (toSheafify J _ ≫ sheafifyMap J
        ((Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom.{u + 1} f))) ≫ eC.hom
    rw [hB, ← toSheafify_naturality, Category.assoc, hC]
    exact h
  change (constantSchemeIso X).hom.app _ ≫ (upperStarFromPoint X).map eB ≫
    (upperStarFromPoint X).map g = _
  rw [← Functor.map_comp, he, Functor.map_comp]
  erw [← Category.assoc,
    ← (constantSchemeIso X).hom.naturality (AddCommGrpCat.ofHom.{u + 1} f)]
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem canonicalRingMap_scalar_natural
    (B C : Type u) [CommRing B] [CommRing C]
    [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalRing B] [IsTopologicalRing C]
    (f : ULift.{u + 1} B →+* ULift.{u + 1} C)
    (g : FiniteDiscreteOrdinary.coefficient B ⟶ FiniteDiscreteOrdinary.coefficient C)
    [IsMonHom g]
    (h : FiniteDiscreteOrdinary.pointConstants B ≫ g.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom.{u + 1} f.toAddMonoidHom) ≫
        FiniteDiscreteOrdinary.pointConstants C) (X : Scheme.{u}) :
    letI : EssentiallySmall.{u + 1} X.ProEt :=
      WeilConjectures.instEssentiallySmallProEt_weilConjectures X
    letI : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
    letI : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
    FiniteDiscreteOrdinary.canonicalRingMap B X ≫
        InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          ((upperStarFromPoint X).map g) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom.{u + 1} f) ≫ FiniteDiscreteOrdinary.canonicalRingMap C X := by
  letI : EssentiallySmall.{u + 1} X.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures X
  letI : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
  letI : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
  let J := Scheme.ProEt.topology X
  let ηB := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of.{u + 1} (ULift.{u + 1} B)))
  let ηC := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of.{u + 1} (ULift.{u + 1} C)))
  let εB := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} B)))
  let εC := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} C)))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (FiniteDiscreteOrdinary.sectionRing C X).property
  ext U a
  have hc := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map
      (CommRingCat.ofHom.{u + 1} f))) U) a
  change (ηC.app U) (f a) =
    (((constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom.{u + 1} f)).hom.app U)
      ((ηB.app U) a) at hc
  have ha := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map
      (AddCommGrpCat.ofHom.{u + 1} f.toAddMonoidHom))) U) a
  change (εC.app U) (f a) =
    (((constantSheaf J Ab.{u + 1}).map
      (AddCommGrpCat.ofHom.{u + 1} f.toAddMonoidHom)).hom.app U) ((εB.app U) a) at ha
  change ((upperStarFromPoint X).map g).hom.app U
    ((FiniteDiscreteOrdinary.canonicalRingMap B X).hom.app U ((ηB.app U) a)) =
      (FiniteDiscreteOrdinary.canonicalRingMap C X).hom.app U
        ((((constantSheaf J CommRingCat.{u + 1}).map
          (CommRingCat.ofHom.{u + 1} f)).hom.app U) ((ηB.app U) a))
  rw [← hc, FiniteDiscreteOrdinary.canonicalRingMap_normalization,
    FiniteDiscreteOrdinary.canonicalRingMap_normalization]
  have hn := congrArg (fun z ↦ z.hom.app U ((εB.app U) a))
    (canonicalAbelianMap_scalar_natural B C f.toAddMonoidHom g h X)
  change ((upperStarFromPoint X).map g).hom.app U
      ((FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom.app U ((εB.app U) a)) =
    (FiniteDiscreteOrdinary.canonicalAbelianMap C X).hom.app U
      ((((constantSheaf J Ab.{u + 1}).map
        (AddCommGrpCat.ofHom.{u + 1} f.toAddMonoidHom)).hom.app U) ((εB.app U) a)) at hn
  rw [← ha] at hn
  exact hn

private theorem normalizationAbIso_eq (X : Scheme.{u}) (A : Type u) [CommRing A] :
    discreteAbIso A X = discreteCoefficientAbelianIso X A := by
  unfold discreteAbIso pointConstantAbIso discreteCoefficientAbelianIso
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem discreteRingIso_normalized (X : Scheme.{u}) (A : Type u) [CommRing A] :
    DiscreteSectionRingNormalized X A (discreteRingIso A X) := by
  intro U a
  simpa only [normalizationAbIso_eq] using discreteRingIso_unit A X U a

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem normalized_unique (X : Scheme.{u}) (A : Type u) [CommRing A]
    {d e : Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X)}
    (hd : DiscreteSectionRingNormalized X A d)
    (he : DiscreteSectionRingNormalized X A e) : d = e := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (InternalAbelianSheafModule.sectionRingSheaf _
      (condensedRingObj (discreteObj A) X)).property
  ext U a
  exact (hd U a).trans (he U a).symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- The ordinary coefficient comparisons and all finite projections are uniquely normalized.
Their data is fixed by the constant sections, before any modules or complexes are considered.

Source: Stacks Tags 099L and 099M, integral-models proof (1)--(2).
(auxiliary; not a blueprint node).

Proof: reconstruct the ring comparisons from the monoidal constant additive comparisons.
Their naturality gives the ordinary first-residue square. The normalized integral section
projection theorem identifies every projection with the specified quotient on constant
sections; the projection equations of the two completion comparisons cancel the intermediate
isomorphisms. This gives the displayed structure. For uniqueness, precompose each of its two
ring isomorphisms with the constant-presheaf sheafification unit. Normalization gives identical
maps there, so the sheafification adjunction identifies the isomorphisms. The remaining fields
are proofs and hence agree by proof irrelevance. This includes zero rings and empty schemes.
-/
theorem integral_constant_section_projection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : ∃! _comparisons : IntegralSectionComparisons l E X, True := by
  have ordinary_projection (n : ℕ) :
      (discreteRingIso.{u} (Padic.coefficientExtensionIntegers l E) X).hom ≫
          sectionMap X (scalarMap l E X) ≫ (completedSectionIso l E X).inv ≫
          limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)) (op n) =
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom.{u + 1} (Ideal.Quotient.mk
            (IntegralConstantCompletion.ideal l E ^ (n + 1)))) := by
    classical
    letI : EssentiallySmall.{u + 1} X.ProEt :=
      WeilConjectures.instEssentiallySmallProEt_weilConjectures X
    letI : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
    letI : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let B := Padic.coefficientExtensionIntegers l E
    let C := Padic.coefficientExtensionRing l E (n + 1)
    let tC : TopologicalSpace C := inferInstance
    let hC : @IsTopologicalRing C tC _ := inferInstance
    letI : Finite C := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI : DiscreteTopology C := finiteTopology_discrete.{u} l E n
    obtain ⟨f⟩ := FiniteDiscreteOrdinary.encoding_exists.{u} C X
    let tB : TopologicalSpace B := by
      letI := spectralNorm.normedField (Padic l) E
      infer_instance
    letI : TopologicalSpace B := tB
    letI : IsTopologicalRing B := by
      letI := spectralNorm.normedField (Padic l) E
      infer_instance
    letI : TopologicalSpace C := tC
    letI : IsTopologicalRing C := hC
    let J := Scheme.ProEt.topology X
    let R := constantSheaf J CommRingCat.{u + 1}
    let g := (IntegralConstantModel.pointComparison l E).inv.hom ≫
      DerivedNakayama.reductionRing l E (n + 1)
    let q : ULift.{u + 1} B →+* ULift.{u + 1} C :=
      ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          ULift.ringEquiv.toRingHom)
    have hg : IsMonHom g := by dsimp only [g]; infer_instance
    letI := hg
    have hconst : FiniteDiscreteOrdinary.pointConstants B ≫ g.hom =
        (Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom.{u + 1} q.toAddMonoidHom) ≫
          FiniteDiscreteOrdinary.pointConstants C := by
      dsimp only [g]
      rw [pointComparison_inv_eq]
      ext S a
      rfl
    have hn := canonicalRingMap_scalar_natural.{u} B C q g hconst X
    have hf : FiniteDiscreteOrdinary.canonicalRingMap C X = f.ringIso.hom := by
      apply Sheaf.hom_ext
      apply sheafify_hom_ext J _ _ (FiniteDiscreteOrdinary.sectionRing C X).property
      ext U a
      exact (FiniteDiscreteOrdinary.canonicalRingMap_normalization C X U a).trans
        (f.normalization U a).symm
    have hscalar : (discreteRingIso.{u} B X).hom ≫ sectionMap X (scalarMap l E X) ≫
        (pointSectionIso.{u} l E X).inv ≫
          InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J
            (AdicCompletion.quotient l E X n) =
        R.map (CommRingCat.ofHom.{u + 1} q) ≫ f.ringIso.hom := by
      have hsc : (discreteRingIso.{u} B X).hom ≫ sectionMap X (scalarMap l E X) =
          FiniteDiscreteOrdinary.canonicalRingMap B X := by
        simpa only [scalarMap, scalarPointMap] using discreteRingIso_scalar.{u} B X
      rw [← Category.assoc, ← Category.assoc, hsc]
      calc
        _ = FiniteDiscreteOrdinary.canonicalRingMap B X ≫
            InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J
              ((upperStarFromPoint X).map g) := by
          rw [Category.assoc]
          apply congrArg (fun z : FiniteDiscreteOrdinary.sectionRing B X ⟶
            FiniteDiscreteOrdinary.sectionRing C X ↦
              FiniteDiscreteOrdinary.canonicalRingMap B X ≫ z)
          ext U a
          exact (congrArg (fun z ↦ z.hom.app U a)
            ((upperStarFromPoint X).map_comp
              (IntegralConstantModel.pointComparison l E).inv.hom
              (DerivedNakayama.reductionRing l E (n + 1)))).symm
        _ = _ := by rw [hn, hf]
    have he : InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J
            (AdicCompletion.quotient l E X n) =
        (integralSectionRingIso.{u} l E X).hom ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n ≫
            f.ringIso.hom :=
      IntegralPresentation.integral_section_projection_normalization.{u} l E X
        (integralEncoding l E X) (integralLimitAbComparison l E X)
        (integralLimitAbComparison_existsUnique l E X).exists.choose_spec
        (integralSectionAbIdentifications l E X).1
        (integralSectionAbIdentifications l E X).2
        (by simpa only [integralEncoding, integralSectionRingIso] using
          (integralSectionRingIso_existsUnique l E X).exists.choose_spec) n f
    let π : Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E) ⟶
        Scheme.adicLisseConstantRing X (IntegralConstantCompletion.integers l E ⧸
          IntegralConstantCompletion.ideal l E ^ (n + 1)) :=
      limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)) (op n)
    let v : CommRingCat.of.{u + 1} (IntegralConstantCompletion.integers l E ⧸
          IntegralConstantCompletion.ideal l E ^ (n + 1)) ≅
        CommRingCat.of.{u + 1} (ULift.{u + 1} C) :=
      (Scheme.integralCoefficientULift l E n).toCommRingCatIso
    have htransport : (completedSectionIso l E X).inv ≫ π ≫ R.map v.hom =
        (pointSectionIso.{u} l E X).inv ≫ (integralSectionRingIso.{u} l E X).hom ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n := by
      apply (cancel_epi (completedSectionIso l E X).hom).mp
      simp only [Iso.hom_inv_id_assoc]
      calc
        π ≫ R.map v.hom = (Scheme.pbcCompletedComparison X
            (Scheme.pbcIntegralDatum l E)).hom ≫ (WeilConjectures.purCoefficientIso l E X).hom ≫
              WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n :=
          (completed_projection l E X n).symm
        _ = _ := by
          unfold completedSectionIso
          simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
            Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    apply (cancel_mono (R.map v.hom ≫ f.ringIso.hom)).mp
    simp only [Category.assoc]
    have ht := congrArg (fun z ↦ (discreteRingIso.{u} B X).hom ≫ sectionMap X (scalarMap l E X) ≫
      z ≫ f.ringIso.hom) htransport
    have hs := hscalar
    rw [he] at hs
    simp only [Category.assoc] at ht hs
    rw [ht, hs]
    rw [← Functor.map_comp_assoc]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact ((Scheme.integralCoefficientULift_exists l E n).exists.choose_spec a).symm
  let canonical : IntegralSectionComparisons l E X :=
    { integers := discreteRingIso (Padic.coefficientExtensionIntegers l E) X
      residue := discreteRingIso (Padic.coefficientExtensionRing l E 1) X
      integers_normalized := discreteRingIso_normalized X _
      residue_normalized := discreteRingIso_normalized X _
      reduction_naturality := discreteRingIso_naturality
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) X
      projection := ordinary_projection }
  refine ⟨canonical, trivial, ?_⟩
  intro comparisons _
  have hi := normalized_unique X (Padic.coefficientExtensionIntegers l E)
    comparisons.integers_normalized canonical.integers_normalized
  have hr := normalized_unique X (Padic.coefficientExtensionRing l E 1)
    comparisons.residue_normalized canonical.residue_normalized
  cases comparisons
  dsimp only [canonical] at hi hr ⊢
  cases hi
  cases hr
  rfl

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
