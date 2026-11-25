/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectStrataUniformReductions
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRealizationDerivedCohomology
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectLocalReductionModels
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectChartComplete
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumLift
import WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement

/-! # The completed local perfect criterion

## References

* Bhatt--Scholze, Proposition 6.6.11
* Bhatt--Scholze, Proposition 6.6.11, with Definition 6.5.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
open ProEtale

private def terminalIdentity (X : Scheme.{u}) : IsTerminal (ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _) (by trivial)) (by
      intro U f
      apply MorphismProperty.Over.Hom.ext
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 X = U.hom at hw
      exact (Category.comp_id _).symm.trans hw)

private theorem completedScalar_eq (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    adicDatumScalar X
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
        quotientFinite := d.quotientFinite } = CompletedConstantReduction.base X d.ideal := by
  apply limit.hom_ext
  intro n
  exact ((adicDatumScalar_exists X
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }).exists.choose_spec n.unop).trans
    (by simpa only [CompletedConstantReduction.base, Opposite.op_unop] using
      ((CompletedConstantReduction.base_exists X d.ideal).choose_spec.1 n.unop).symm)

private def ordinaryConstantModel (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    integralConstantModule T d ≅ adicLisseConstantModules T A ⋙
      pbcExtend (CompletedConstantReduction.base T d.ideal ≫
        (pbcCompletedComparison T d).hom) := by
  let b := CompletedConstantReduction.base T d.ideal
  let j := pbcCompletedComparison T d
  let e := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j.symm)
  let c : pbcRestrict j.inv ≅ pbcExtend j.hom :=
    e.toAdjunction.leftAdjointUniq (pbcScalarAdjunction j.hom)
  let t : pbcExtend b ⋙ pbcExtend j.hom ≅ pbcExtend (b ≫ j.hom) :=
    ((pbcScalarAdjunction b).comp (pbcScalarAdjunction j.hom)
      |>.ofNatIsoRight (pbcRestrictComp b j.hom (b ≫ j.hom) rfl)).leftAdjointUniq
        (pbcScalarAdjunction (b ≫ j.hom))
  have h : integralConstantModule T d =
      (adicLisseConstantModules T A ⋙ pbcExtend b) ⋙ pbcRestrict j.inv := by
    dsimp only [integralConstantModule, completedKoszulConstant]
    rw [completedScalar_eq]
    rfl
  exact eqToIso h ≪≫ Functor.isoWhiskerLeft _ c ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ t

private theorem perfectConstantModel (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P) :
    Nonempty ((integralConstantDerived T d).obj P ≅
      (pbcDerivedExtend (CompletedConstantReduction.base T d.ideal ≫
        (pbcCompletedComparison T d).hom)).obj
          (DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex T A).obj
            (DerivedCategory.Q.objPreimage P)))) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  obtain ⟨C, a, b, ha, hb, hC, ⟨ep⟩⟩ := hP
  let := hb
  let F := adicLisseConstantModules T A
  have : F.Additive := CompletedConstantReduction.constant_additive T A
  have : PreservesFiniteLimits F := (CompletedConstantReduction.constant_exact T A).1
  have : PreservesFiniteColimits F := (CompletedConstantReduction.constant_exact T A).2
  let c := CompletedConstantReduction.base T d.ideal ≫ (pbcCompletedComparison T d).hom
  let C₀ := (CompletedConstantReduction.constantComplex T A).obj C
  have : IsIso (pbcComplexCounit c C₀) := by
    have := pbcExtensionCounit_isIso c C₀ (constant_kflat T C b (fun q ↦ (hC q).1))
    dsimp only [pbcComplexCounit]
    infer_instance
  let ec : DerivedCategory.Q.obj
      ((CompletedConstantReduction.constantComplex T A).obj (DerivedCategory.Q.objPreimage P))
      ≅ DerivedCategory.Q.obj C₀ :=
    (F.mapDerivedCategoryFactors.app _).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso P ≪≫ ep) ≪≫
        F.mapDerivedCategoryFactors.app C
  refine ⟨(integralConstantDerived T d).mapIso ep ≪≫
    (integralRealizationFactors T d).app C ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (ordinaryConstantModel T d) (.up ℤ)).app C) ≪≫
    (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (F ⋙ pbcExtend c)) (.up ℤ)).app C)).symm ≪≫
    (asIso (pbcComplexCounit c C₀)).symm ≪≫ (pbcDerivedExtend c).mapIso ec.symm⟩

private theorem perfect_uniformProfile (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : IsIntegralStratifiedPerfect T d K) :
    PbcUniformReductionProfile T d K := by
  classical
  obtain ⟨s, hs⟩ := hK
  choose W hW hw using hs
  let e (i : Fin s.n) : ProEt.mk (𝟙 (s.domain i)) ≅ ⊤_ (s.domain i).ProEt :=
    (terminalIdentity _).uniqueUpToIso terminalIsTerminal
  have covers (i : Fin s.n) : ∃ R : Presieve (ProEt.mk (𝟙 (s.domain i))),
      R ∈ ProEt.precoverage (s.domain i) _ ∧ R ≤ (W i).pullback (e i).hom := by
    have : (ProEt.precoverage (s.domain i)).IsStableUnderComposition := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).IsStableUnderBaseChange := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).HasIsos := by
      dsimp [ProEt.precoverage]; infer_instance
    exact (ProEt.precoverage (s.domain i)).mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      ((ProEt.topology (s.domain i)).pullback_stable (e i).hom (hW i))
  choose R hR hRW using covers
  let V (i : Fin s.n) := (R i).preZeroHypercover
  have hcover (i : Fin s.n) :
      Presieve.ofArrows (V i).X (V i).f ∈ ProEt.precoverage (s.domain i) _ := by
    change (V i).presieve₀ ∈ _
    rw [Presieve.presieve₀_preZeroHypercover]
    exact hR i
  have hmodel (i : Fin s.n) (j : (V i).I₀) :=
    hw i ((V i).X j) ((V i).f j ≫ (e i).hom) (hRW i _ _ j.2)
  have hraw (i : Fin s.n) (j : (V i).I₀) :
      ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
        @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P ∧
        Nonempty (integralLocalDerived (s.immersion i) (pbcAdicCompletion T d)
          ((V i).X j) K ≅
          integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) ((V i).X j)
            ((pbcDerivedExtend (CompletedConstantReduction.base T d.ideal ≫
              (pbcCompletedComparison T d).hom)).obj (DerivedCategory.Q.obj
                ((CompletedConstantReduction.constantComplex T A).obj
                  (DerivedCategory.Q.objPreimage P))))) := by
    obtain ⟨P, hP, ⟨c⟩⟩ := hmodel i j
    obtain ⟨b⟩ := perfectConstantModel T d P hP
    exact ⟨P, hP, ⟨c ≪≫ localMapIso (s.immersion i) (pbcAdicCompletion T d)
      ((V i).X j) b⟩⟩
  obtain ⟨⟨a, b, hab, hKzero, hzero⟩, hc, _⟩ :=
    perfect_strata_uniform_reductions T d K s.toFiniteLocallyClosed
      (fun i ↦ (V i).I₀) (fun i ↦ (V i).X) (fun i ↦ (V i).f) hcover hraw
  let G (n : ℕ) := pbcRestrict (pbcLevelConstantComparison T d n).hom
  let eh (n : ℕ) (q : ℤ) := ((G n).mapDerivedCategoryHomologyFunctorIso q).app
    ((pbcCompletedReduction T d n).obj K)
  refine ⟨a, b, fun n ↦ ⟨?_, ?_, ?_⟩⟩
  · apply (DerivedCategory.isGE_iff _ a).2
    intro q hq
    exact ((G n).map_isZero (hzero n q (Or.inl hq))).of_iso (eh n q).symm
  · apply (DerivedCategory.isLE_iff _ b).2
    intro q hq
    exact ((G n).map_isZero (hzero n q (Or.inr hq))).of_iso (eh n q).symm
  · intro q
    obtain ⟨S, hn, hS, hm⟩ := hc n q
    refine ⟨S, hn, hS, fun i ↦ ?_⟩
    obtain ⟨W, hW, hmodels⟩ := hm i
    refine ⟨W, hW, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨c⟩⟩ := hmodels U f hf
    exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage (S.immersion i)
        (adicLisseConstantRing T (PbcQuotient d n))).mapIso (eh n q).symm) ≪≫ c⟩⟩

private theorem perfect_intrinsicComplete (T : Scheme.{u}) [IsNoetherian T]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K := by
  classical
  let d := pbcIntegralDatum l E
  obtain ⟨s, hs⟩ := hK
  choose W hW hw using hs
  let e (i : Fin s.n) : ProEt.mk (𝟙 (s.domain i)) ≅ ⊤_ (s.domain i).ProEt :=
    (terminalIdentity _).uniqueUpToIso terminalIsTerminal
  have covers (i : Fin s.n) : ∃ R : Presieve (ProEt.mk (𝟙 (s.domain i))),
      R ∈ ProEt.precoverage (s.domain i) _ ∧ R ≤ (W i).pullback (e i).hom := by
    have : (ProEt.precoverage (s.domain i)).IsStableUnderComposition := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).IsStableUnderBaseChange := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).HasIsos := by
      dsimp [ProEt.precoverage]; infer_instance
    exact (ProEt.precoverage (s.domain i)).mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      ((ProEt.topology (s.domain i)).pullback_stable (e i).hom (hW i))
  choose R hR hRW using covers
  let H (i : Fin s.n) := (R i).preZeroHypercover
  let F (i : Fin s.n) := ProEt.forget (s.domain i) ⋙ Over.forget (s.domain i)
  let V (i : Fin s.n) : Scheme.Cover.{u + 1} proetalePrecoverage (s.domain i) :=
    { toPreZeroHypercover := (H i).map (F i)
      mem₀ := by
        rw [PreZeroHypercover.presieve₀_map, Presieve.presieve₀_preZeroHypercover]
        exact hR i }
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  apply (wfComplete_iff_presentation T d r a ha K).mp
  apply (stratum_completion_unit_restriction d T s.toFiniteLocallyClosed V r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)).mpr
  intro i j C eC
  change Fin s.n at i
  have := s.isImmersion i
  obtain ⟨P, hP, he⟩ := hw i ((H i).X j) ((H i).f j ≫ (e i).hom) (hRW i _ _ j.2)
  have hf : (V i).f j = ((H i).X j).hom := by
    have hh := MorphismProperty.Over.w ((H i).f j)
    change ((H i).f j).left ≫ 𝟙 (s.domain i) = ((H i).X j).hom at hh
    change ((H i).f j).left = ((H i).X j).hom
    exact (Category.comp_id ((H i).f j).left).symm.trans hh
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hlocal (f : ((H i).X j).left ⟶ s.domain i)
      (eC : DerivedCategory.Q.obj C ≅ (d.pull (f ≫ s.immersion i)).obj K)
      (hf : f = ((H i).X j).hom) :
      IsDerivedCompleteIntrinsic ((H i).X j).left d r a ha
        ((d.pull (f ≫ s.immersion i)).obj K) C eC := by
    subst f
    exact integralPerfectChart_complete T l E (s.immersion i) ((H i).X j) K P hP he
      r a ha C eC
  exact hlocal ((V i).f j) eC hf

private theorem integralIdeal_maximal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (pbcIntegralDatum l E).ideal.IsMaximal := by
  let h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hπ : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let e : Padic.coefficientExtensionIntegers l E ≃+* PbcIntegralRing l E :=
    ULift.ringEquiv.symm
  have hmap : Ideal.map e.toRingHom (Padic.coefficientExtensionMaximalIdeal l E) =
      (pbcIntegralDatum l E).ideal := by
    rw [← hπ]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← hmap]
  exact Ideal.IsMaximal.map_bijective e.toRingHom e.bijective hm

private theorem uniform_complete_perfect (T : Scheme.{u}) [IsNoetherian T]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hcomplete : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K)
    (hprofile : PbcUniformReductionProfile T (pbcIntegralDatum l E) K) :
    IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K := by
  classical
  let d := pbcIntegralDatum l E
  let k := PbcQuotient d 0
  let : (d.ideal ^ (0 + 1)).IsMaximal := by simpa only [Nat.zero_add, pow_one]
    using (integralIdeal_maximal l E)
  let : Field k := Ideal.Quotient.field _
  let : Finite k := d.quotientFinite 0
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot _
  obtain ⟨C, ⟨L, hL, ⟨eL⟩⟩, ⟨eC⟩⟩ :=
    (uniformProfile_localEffectivity T d K hprofile).1 0
  have hc (q : ℤ) : IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj L) := by
    obtain ⟨s, hs, hm⟩ := hL.1 q
    exact ⟨s, hm⟩
  obtain ⟨s, hs, hm⟩ := finite_field_stratified_perfect_models T k L hL.2 hc
  refine ⟨s.withConstructibleStrata hs, fun i ↦ ?_⟩
  have := s.isImmersion i
  have : IsLocallyNoetherian (s.domain i) :=
    LocallyOfFiniteType.isLocallyNoetherian (s.immersion i)
  have : TopologicalSpace.NoetherianSpace (s.domain i) :=
    (s.immersion i).isEmbedding.isInducing.noetherianSpace
  obtain ⟨𝒰, h𝒰⟩ := hm i
  apply integralResidueStratum_lift T l E K hcomplete (s.domain i) (s.immersion i) 𝒰 C ⟨eC⟩
  intro j
  obtain ⟨P, a, b, ha, hb, hfinite, hP, he, he'⟩ := h𝒰 j
  obtain ⟨e⟩ := he'
  exact ⟨P, hP, ⟨(finiteCoefficientDerivedPullback T k
    (𝒰.f j ≫ s.immersion i)).mapIso eL.symm ≪≫ e⟩⟩

/-- The completed reduction-tower category has the local perfect description.
This is Proposition 6.6.11 alone, before the cohomology characterization of 6.8.11(3). -/
theorem integralCompletedLocalPerfectCriterion
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤)))
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K := by
  constructor
  · rintro ⟨hcomplete, hmodels, horigins⟩
    exact uniform_complete_perfect T l E K hcomplete
      ((pbcUniformReductionCriterion l E T K).mp ⟨hmodels, horigins⟩)
  · intro hK
    exact ⟨perfect_intrinsicComplete T l E K hK,
      (pbcUniformReductionCriterion l E T K).mpr (perfect_uniformProfile T _ K hK)⟩

end AlgebraicGeometry.Scheme
