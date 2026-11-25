/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfect
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.CompletedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReduction
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import all WeilConjectures.AlgebraicGeometry.ScalarModelFiniteFlatResolution
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModules
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The integral cohomological adic criterion

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), using Definition 6.5.1,
Remark 6.3.2 and Proposition 6.6.11; Stacks Project, Tag 09C0
(auxiliary; not a blueprint node).

The completed ring is the actual limit of positive constant quotients. ULift only places
scalars in the sheaf universe. The residue quotient and its finite Tor condition are those
of the published adic-constructibility predicate, without any dimension or characteristic
restriction on the Noetherian scheme.

## Main definitions

* `WeilConjectures.sfAbBijective`: the canonical small-site instance at the fixed coefficient size.

## Main statements

* `integral_cohomological_adic_criterion`: the cohomological integral criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

attribute [local instance 3000] WeilConjectures.sfAbBijective

private theorem constantExact (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (adicLisseConstantModules X A) ∧
      PreservesFiniteColimits (adicLisseConstantModules X A) :=
  CompletedConstantReduction.constant_exact X A

private theorem scalarExact (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    PreservesFiniteLimits (completedAdicChange X (CompletedConstantReduction.base X I)) ∧
      PreservesFiniteColimits
        (completedAdicChange X (CompletedConstantReduction.base X I)) := by
  have h := completed_constant_algebra_flat_quotients X I _ (Iso.refl _)
    (CompletedConstantReduction.base X I)
    (fun n ↦ by simpa [CompletedConstantReduction.base] using
      (CompletedConstantReduction.base_exists X I).choose_spec.1 n)
  exact (exactFunctor_iff _).mp h.2.1

private noncomputable def scalarFunctor (X : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :=
  adicLisseConstantModules X A ⋙ completedAdicChange X (CompletedConstantReduction.base X I)

private instance scalarFunctor_additive (X : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) : (scalarFunctor X I).Additive := by
  have := CompletedConstantReduction.constant_additive X A
  unfold scalarFunctor
  infer_instance

private instance scalarFunctor_limits (X : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    PreservesFiniteLimits (scalarFunctor X I) := by
  have := (constantExact X A).1
  have := (scalarExact X I).1
  exact comp_preservesFiniteLimits _ _

private instance scalarFunctor_colimits (X : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    PreservesFiniteColimits (scalarFunctor X I) := by
  have := (constantExact X A).2
  have := (scalarExact X I).2
  exact comp_preservesFiniteColimits _ _

private noncomputable def inverseImageIdentityIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback i R
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage i R := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let H := proEtaleModuleInverseImage i R
  let r : SheafOfModules.restrictScalars ((adicLisseForget S).map (𝟙 B)) ≅
      𝟭 (proEtaleRingModules S B) :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun U ↦ ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
          (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  let a := proEtaleRingExtensionAdjunction i R B (Iso.refl _)
  let b := (Adjunction.id (C := proEtaleRingModules S B)).ofNatIsoRight r.symm
  exact Functor.isoWhiskerLeft H (a.leftAdjointUniq b) ≪≫ Functor.rightUnitor H

private instance criterionSliceDerived (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}) (U : S.ProEt) :
    HasDerivedCategory (SheafOfModules.{u + 1} (((adicLisseForget S).obj R).over U)) :=
  HasDerivedCategory.standard _

private noncomputable def restrictionFunctor {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt) :=
  proEtaleModuleInverseImage i R ⋙
    SheafOfModules.localizedSystemRestriction.{u + 1, u, 0}
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) U

private instance restrictionFunctor_additive {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt) :
    (restrictionFunctor i R U).Additive := by
  have := (proEtaleModuleInverseImageAdjunction i R).left_adjoint_additive
  unfold restrictionFunctor
  infer_instance

private instance restrictionFunctor_limits {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt) :
    PreservesFiniteLimits (restrictionFunctor i R U) := by
  have := proEtaleModuleInverseImage_preservesFiniteLimits i R
  exact comp_preservesFiniteLimits _ _

private instance restrictionFunctor_colimits {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt) :
    PreservesFiniteColimits (restrictionFunctor i R U) := by
  have := (proEtaleModuleInverseImageAdjunction i R).leftAdjoint_preservesColimits
  exact comp_preservesFiniteColimits _ _

private noncomputable def localRestrictionIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :
    sfbLocalRestriction i R U K ≅ (restrictionFunctor i R U).mapDerivedCategory.obj K := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let G := proEtaleRingModulePullback i R B (Iso.refl _)
  let H := proEtaleModuleInverseImage i R
  let T := SheafOfModules.localizedSystemRestriction.{u + 1, u, 0} B U
  let e : G ≅ H := inverseImageIdentityIso i R
  have : H.Additive := (proEtaleModuleInverseImageAdjunction i R).left_adjoint_additive
  let C := DerivedCategory.Q.objPreimage K
  let L := G.mapDerivedCategory.obj K
  let D := DerivedCategory.Q.objPreimage L
  change DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj D) ≅ _
  refine (T.mapDerivedCategoryFactors.app D).symm ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L) ≪≫
    T.mapDerivedCategory.mapIso
      (G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm) ≪≫
    T.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app C) ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app C)) ≪≫
    (T.mapDerivedCategoryFactors.app _ ) ≪≫ ?_
  exact ((restrictionFunctor i R U).mapDerivedCategoryFactors.app C).symm ≪≫
    (restrictionFunctor i R U).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso K)

private abbrev scalarDouble {A : Type*} [Category* A] [HasZeroMorphisms A]
    [HasZeroObject A] {X Y : A} (f : X ⟶ Y) : CochainComplex A ℤ :=
  HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)

private theorem scalarAugmentation {A : Type*} [Category* A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ ε : scalarDouble S.f ⟶ (CochainComplex.singleFunctor A 0).obj S.X₃,
      QuasiIso ε :=
  SheafOfModules.twoTerm_augmentation S hS

private theorem scalarPerfectPresentation (A : Type (u + 1)) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj M ≅ DerivedCategory.Q.obj P) := by
  classical
  obtain ⟨n, _, q, _, hq, _⟩ := Module.FinitePresentation.exists_fin' A M
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun A (Fin n)) (LinearMap.ker q)
  let f := (LinearMap.ker q).subtype.comp b.equivFun.symm.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp b.equivFun.symm.injective
  have hfq : q.comp f = 0 := by
    apply LinearMap.ext
    intro x
    exact (b.equivFun.symm x).property
  let S := ShortComplex.moduleCatMk f q hfq
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 hf
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hq
    refine ⟨(ShortComplex.moduleCat_exact_iff _).2 ?_⟩
    intro x hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
    simp
  let P := scalarDouble S.f
  obtain ⟨ε, hε⟩ := scalarAugmentation S hS
  have ha : P.IsStrictlyGE (-1) := (P.isStrictlyGE_iff _).2
    (fun i hi ↦ HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega))
  have hb : P.IsStrictlyLE 0 := (P.isStrictlyLE_iff _).2
    (fun i hi ↦ HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega))
  refine ⟨P, -1, 0, ha, hb, ?_, ?_⟩
  · intro i
    by_cases hm : i = -1
    · subst i
      let e := HomologicalComplex.doubleXIso₀ S.f
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
      have : Module.Projective A S.X₁ := by
        change Module.Projective A (Fin m → A)
        infer_instance
      have : Module.Finite A S.X₁ := by
        change Module.Finite A (Fin m → A)
        infer_instance
      exact ⟨Module.Projective.of_equiv' e.toLinearEquiv.symm,
        Module.Finite.equiv e.toLinearEquiv.symm⟩
    by_cases h0 : i = 0
    · subst i
      let e := HomologicalComplex.doubleXIso₁ S.f
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide : (-1 : ℤ) ≠ 0)
      have : Module.Projective A S.X₂ := by
        change Module.Projective A (Fin n → A)
        infer_instance
      have : Module.Finite A S.X₂ := by
        change Module.Finite A (Fin n → A)
        infer_instance
      exact ⟨Module.Projective.of_equiv' e.toLinearEquiv.symm,
        Module.Finite.equiv e.toLinearEquiv.symm⟩
    · have hz : IsZero (P.X i) :=
        HomologicalComplex.isZero_double_X S.f (by decide) i hm h0
      have := ModuleCat.subsingleton_of_isZero hz
      exact ⟨inferInstance, inferInstance⟩
  · have := hε
    exact ⟨(DerivedCategory.singleFunctorIsoCompQ _ 0).app M ≪≫
      (asIso (DerivedCategory.Q.map ε)).symm⟩

private noncomputable def completedModelIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    sfbCompletedModel X I P ≅
      (scalarFunctor X I).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  ((scalarFunctor X I).mapDerivedCategoryFactors.app P).symm

private noncomputable def completedModelHomologyIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj (sfbCompletedModel X I P) ≅
      (scalarFunctor X I).obj (P.homology q) :=
  (DerivedCategory.homologyFunctor _ q).mapIso (completedModelIso X I P) ≪≫
    ((scalarFunctor X I).mapDerivedCategoryHomologyFunctorIso q).symm.app
      (DerivedCategory.Q.obj P) ≪≫
    (scalarFunctor X I).mapIso ((DerivedCategory.homologyFunctorFactors _ q).app P)

private noncomputable def localHomologyIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K L : DerivedCategory (proEtaleRingModules X R))
    (e : sfbLocalRestriction i R U K ≅ sfbLocalRestriction i R U L) (q : ℤ) :
    (restrictionFunctor i R U).obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (restrictionFunctor i R U).obj ((DerivedCategory.homologyFunctor _ q).obj L) :=
  ((restrictionFunctor i R U).mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((localRestrictionIso i R U K).symm ≪≫ e ≪≫ localRestrictionIso i R U L) ≪≫
    ((restrictionFunctor i R U).mapDerivedCategoryHomologyFunctorIso q).symm.app L

private theorem perfectCohomologyFinitePresentation {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) (q : ℤ) :
    Module.FinitePresentation A (P.homology q) := by
  have := (hP q).2
  have : Module.Finite A (P.cycles q) :=
    Module.Finite.of_injective (P.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite A (P.homology q) :=
    Module.Finite.of_surjective (P.homologyπ q).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.finitePresentation_of_finite A _

private instance integersDomain (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsDomain (ProEtale.IntegralConstantCompletion.integers l E) :=
  MulEquiv.isDomain (Padic.coefficientExtensionIntegers l E) ULift.ringEquiv.toMulEquiv

private theorem integralCoefficients (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsDiscreteValuationRing (ProEtale.IntegralConstantCompletion.integers l E) ∧
    IsAdicComplete (ProEtale.IntegralConstantCompletion.ideal l E)
      (ProEtale.IntegralConstantCompletion.integers l E) ∧
    ((ProEtale.IntegralConstantCompletion.ideal l E).IsMaximal ∧
      ∀ J : Ideal (ProEtale.IntegralConstantCompletion.integers l E),
        J.IsMaximal → J = ProEtale.IntegralConstantCompletion.ideal l E) := by
  let O := Padic.coefficientExtensionIntegers l E
  let R := ProEtale.IntegralConstantCompletion.integers l E
  let I := ProEtale.IntegralConstantCompletion.ideal l E
  let J : Ideal O := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  let e : O ≃+* R := ULift.ringEquiv.symm
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  let : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hJ : J = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hI : J.map e = I := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hc : IsAdicComplete J O := hJ.symm ▸ Padic.coefficientIntegers_complete l E
  have hcR : IsAdicComplete I R :=
    hI ▸ (IsAdicComplete.congr_ringEquiv J e).mpr hc
  have hm : I.IsMaximal := by
    rw [← hI]
    have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
    rw [← hJ] at hm
    exact hm.map_bijective e e.bijective
  exact ⟨inferInstance, hcR, hm, fun Q hQ ↦
    (IsLocalRing.eq_maximalIdeal hQ).trans (IsLocalRing.eq_maximalIdeal hm).symm⟩

private theorem completedStratified_of_perfect (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) (q : ℤ) :
    IsCompletedConstantStratified X I ((DerivedCategory.homologyFunctor _ q).obj K) := by
  obtain ⟨s, hs, hmodel⟩ := hK
  let t : FiniteLocallyClosedStratification X :=
    { n := s.n
      stratum := s.stratum
      isLocallyClosed_stratum := s.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
      domain := s.domain
      immersion := s.immersion
      isImmersion := s.isImmersion
      range_immersion := s.range_immersion }
  refine ⟨t, hs, ?_⟩
  intro a
  obtain ⟨V, hV, hmodel⟩ := hmodel a
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, b, c, _, hb, hc, hP, ⟨e⟩⟩ := hmodel U f hf
  refine ⟨P.homology q, perfectCohomologyFinitePresentation P hP q, ?_⟩
  exact ⟨localHomologyIso (s.immersion a) _ U K _ e q ≪≫
    (restrictionFunctor (s.immersion a) _ U).mapIso (completedModelHomologyIso X I P q)⟩

private theorem perfect_of_completedStratified (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (u + 1)} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (I : Ideal A) (M : proEtaleRingModules X (adicLisseCompletedRing X I))
    (hM : IsCompletedConstantStratified X I M) :
    IsSfbStratifiedPerfect X I ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨s, hs, hmodel⟩ := hM
  let t := Stratification.ofNoetherianSpace s.n s.stratum s.isLocallyClosed_stratum
    s.iUnion_stratum_eq_univ s.pairwise_disjoint_stratum s.domain s.immersion
    s.isImmersion s.range_immersion
  refine ⟨t, hs, ?_⟩
  intro a
  obtain ⟨V, hV, hmodel⟩ := hmodel a
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, hP, ⟨e⟩⟩ := hmodel U f hf
  have := hP
  obtain ⟨C, b, c, hb, hc, hC, ⟨α⟩⟩ := scalarPerfectPresentation A P
  let F := scalarFunctor X I
  let G := restrictionFunctor (s.immersion a) (adicLisseCompletedRing X I) U
  let β : (DerivedCategory.singleFunctor _ 0).obj (F.obj P) ≅
      sfbCompletedModel X I C :=
    (F.mapDerivedCategorySingleFunctor 0).symm.app P ≪≫
      F.mapDerivedCategory.mapIso α ≪≫ (completedModelIso X I C).symm
  refine ⟨C, b, c, ⟨C, b, c, hb, hc, hC, ⟨Iso.refl _⟩⟩, hb, hc, hC, ?_⟩
  exact ⟨localRestrictionIso (s.immersion a) _ U _ ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
    (G.mapDerivedCategorySingleFunctor 0).symm.app (F.obj P) ≪≫
    G.mapDerivedCategory.mapIso β ≪≫ (localRestrictionIso (s.immersion a) _ U _).symm⟩

private theorem completedStratified_of_iso {X : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] {I : Ideal A}
    {M N : proEtaleRingModules X (adicLisseCompletedRing X I)} (e : M ≅ N)
    (hM : IsCompletedConstantStratified X I M) : IsCompletedConstantStratified X I N := by
  obtain ⟨s, hs, hmodel⟩ := hM
  refine ⟨s, hs, ?_⟩
  intro a
  obtain ⟨V, hV, hmodel⟩ := hmodel a
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, hP, ⟨α⟩⟩ := hmodel U f hf
  exact ⟨P, hP, ⟨(restrictionFunctor (s.immersion a) _ U).mapIso e.symm ≪≫ α⟩⟩

/-- Bounded cohomology with finite constant stratified models is equivalent to local
uniformizer-adic completeness and bounded constructible etale origin of the first derived
reduction, with finite Tor amplitude. Here `IsSfbAdicConstructible` includes the actual
coefficient-linear derived isomorphism and tests tensor with every degree-zero etale
residue-module sheaf. Torsion finitely presented integer modules are allowed.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), Definition 6.5.1,
Remark 6.3.2 and Proposition 6.6.11; Stacks Tag 09C0
(auxiliary; not a blueprint node).

Proof:
1. The extension-integers DVR theorem makes R Noetherian. Write r = |pi| < 1.
Compatible residue lifts x_n satisfy |x_m-x_n| <= r^n for m >= n. Completeness of E
and the nonarchimedean inequality give a limit in R realizing every residue. The
intersection of all pi^n R is zero by the same estimate. Thus R is pi-adically complete.
The integral-coefficient-limit theorem identifies the given coefficients with B, and
integral-criterion-constant-coefficients supplies flatness of R_X -> B and B/pi = k_X.
These are the coefficient hypotheses of lem-sfb-adic-stratified-perfect; its condition
(a), IsSfbAdicConstructible, is precisely the right hand side here.
2. A finite presentation of an R-module P gives a finite surjection R^m -> P.
Its kernel N is finite by lem-weil-pbc-noetherian-submodule-finite and torsion-free
as a submodule of R^m. By lem-sc-dvr-fg-torsionfree-free it is finite free. Hence
[N -> R^m] in degrees -1,0 resolves P, including torsion P. Constant-module-section-
properties preserves this exact sequence, and flatness of B over R_X preserves it
after scalar extension. Thus B tensor_R P has a two-term finite free model.
3. On every constructible stratum the cohomology sheaf has these constant local
models. Step 2 and (b) implies (a) of lem-sfb-adic-stratified-perfect show that a
constructible module in degree zero satisfies the right hand side.
4. For bounded K, choose cohomological bounds u <= v. Starting with tau_{<=u-1}K = 0,
apply theorem-pbc-injective-acyclicity successively for q = u,...,v. Each third term
H^q(K)[-q] satisfies (a) by step 3 and shift closure. The triangulated closure of
lem-sfb-adic-stratified-perfect gives (a) for tau_{<=v}K, hence for K.
5. Conversely that lemma gives boundedness and stratified perfect R-complex models.
Proetale-immersion-limit-preservation identifies inverse-image B with the completion
on each stratum and makes module restriction exact; ringed-derived-restriction gives
exact slice restriction. Constant-module-section-properties and coefficient flatness
identify local cohomology with B tensor_R H^q(P). Noetherian-submodule-finite makes
kernels and images in the finite projective terms finite; their cohomology quotients
are finite and hence finitely presented by noetherian-finite-module-finite-presentation.
These are precisely IsCompletedConstantStratified's models for every cohomology sheaf.
Together with boundedness this proves the left hand side. -/
theorem integral_cohomological_adic_criterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (proEtaleRingModules X
      (adicLisseCompletedRing X (ProEtale.IntegralConstantCompletion.ideal l E)))) :
    (DerivedCategory.TStructure.t.bounded K ∧
      ∀ q : ℤ, IsCompletedConstantStratified X
        (ProEtale.IntegralConstantCompletion.ideal l E)
        ((DerivedCategory.homologyFunctor _ q).obj K)) ↔
      IsSfbAdicConstructible X (ProEtale.IntegralConstantCompletion.ideal l E) K := by
  let R := ProEtale.IntegralConstantCompletion.integers l E
  let I := ProEtale.IntegralConstantCompletion.ideal l E
  obtain ⟨hR, hc, hI⟩ := integralCoefficients l E
  have : IsDiscreteValuationRing R := hR
  have : IsAdicComplete I R := hc
  obtain ⟨hequiv, hbounded, hzero, hiso, hshift, htriangle⟩ :=
    adic_stratified_perfect X R I hI
  let P : ObjectProperty (proEtaleRingModules X (adicLisseCompletedRing X I)) :=
    IsCompletedConstantStratified X I
  let Q : ObjectProperty (DerivedCategory
      (proEtaleRingModules X (adicLisseCompletedRing X I))) := IsSfbAdicConstructible X I
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ completedStratified_of_iso e h⟩
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hiso _ _ ⟨e⟩ h⟩
  constructor
  · rintro ⟨hb, hcoh⟩
    apply DerivedCategory.prop_of_bounded_of_degreewise Q
      (fun L hL ↦ hiso _ L ⟨(isZero_zero _).isoZero ≪≫ hL.isoZero.symm⟩ hzero)
      (fun T hT h₁ h₃ ↦ (htriangle T hT).2.2 ⟨h₃, h₁⟩) (fun _ ↦ P) ?_ K hb hcoh
    intro q M hM
    have h₀ : Q ((DerivedCategory.singleFunctor _ 0).obj M) :=
      (hequiv _).2 (perfect_of_completedStratified X I M hM)
    exact hiso _ _
      ⟨((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by omega)).app M⟩
      (hshift _ (-q) h₀)
  · intro hK
    obtain ⟨a, b, _, ha, hb⟩ := hbounded K hK
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩,
      fun q ↦ completedStratified_of_perfect X I K ((hequiv K).1 hK) q⟩

end AlgebraicGeometry.Scheme
