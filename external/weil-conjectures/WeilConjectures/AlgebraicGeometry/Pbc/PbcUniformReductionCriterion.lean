/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformLocalModelCohomology

import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedConstructibleTowerLocalEffectivity
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations

/-! # A uniform cohomology criterion for compatible constructible reductions -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
open ProEtale

private theorem uniformProfile_localEffectivity
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : PbcUniformReductionProfile T d K) :
    (∀ n : ℕ, IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin T d
      (pbcReductionAdicTower T d K) n) ∧
      IsUniformlyBoundedConstructibleAdicTower d (pbcReductionAdicTower T d K) := by
  obtain ⟨a, b, h⟩ := hK
  let R (n : ℕ) := pbcRestrict (pbcLevelConstantComparison T d n).hom
  have e (n : ℕ) (q : ℤ) :=
    ((R n).mapDerivedCategoryHomologyFunctorIso q).app
      ((pbcCompletedReduction T d n).obj K)
  apply normalizedConstructibleTower_local_effectivity T d (pbcReductionAdicTower T d K)
    ?_ (min a b) b (min_le_right _ _) ?_
  · intro n q
    change IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient d n)
      ((R n).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T d n).obj K)))
    have hconstructible := (h n).2.2 q
    obtain ⟨S, hn, hc, hS⟩ := hconstructible
    refine ⟨S, hn, hc, fun i ↦ ?_⟩
    obtain ⟨V, hV, htriv⟩ := hS i
    refine ⟨V, hV, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := htriv U f hf
    exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage (S.immersion i)
        (adicLisseConstantRing T (PbcQuotient d n))).mapIso (e n q)) ≪≫ eM⟩⟩
  · intro n q hq
    have hz : Limits.IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcConstantReduction T d n).obj K)) := by
      rcases hq with hqa | hqb
      · exact (DerivedCategory.isGE_iff _ a).1 (h n).1 q
          (lt_of_lt_of_le hqa (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff _ b).1 (h n).2.1 q hqb
    have hr := hz.of_iso (e n q)
    let H := (DerivedCategory.homologyFunctor _ q).obj
      ((pbcCompletedReduction T d n).obj K)
    change Limits.IsZero H
    have : (R n).ReflectsIsomorphisms :=
      (proEtaleRingRestrictScalars_properties (pbcLevelConstantComparison T d n).hom).2.2
    have hz : IsIso ((R n).map (0 : H ⟶ H)) := hr.isIso hr _
    have : IsIso (0 : H ⟶ H) := isIso_of_reflects_iso _ (R n)
    exact (Limits.isIsoZero_iff_source_target_isZero H H).1 inferInstance |>.1

private theorem uniformProfile_uniformReductions
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : PbcUniformReductionProfile T d K) :
    PbcHasUniformConstructibleReductions T d K := by
  refine ⟨pbcReductionAdicTower T d K, fun _ ↦ Iso.refl _,
    (uniformProfile_localEffectivity T d K hK).2, ?_⟩
  intro b a hab
  dsimp only [pbcReductionAdicTower, Iso.refl_hom]
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  dsimp only [adicTowerSemilinearTransition, pbcReductionNormalization,
    pbcReductionNormalizationHom]
  exact (pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).homEquiv
    _ _ |>.apply_symm_apply _

private theorem etaleComparison_liftIso (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (X Y : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hX : DerivedCategory.TStructure.t.plus X)
    (hY : DerivedCategory.TStructure.t.plus Y)
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj X ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj Y) :
    ∃ β : X ≅ Y,
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map β.hom =
        e.hom := by
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := finiteCoefficientRealization T A
  let H := finiteCoefficientComparison T A
  let c := (CategoryTheory.Functor.mapDerivedCategoryCompIso G R).symm
  let e' : H.mapDerivedCategory.obj X ≅ H.mapDerivedCategory.obj Y :=
    c.app X ≪≫ R.mapDerivedCategory.mapIso e ≪≫ (c.app Y).symm
  let X' : DerivedCategory.Plus _ := ⟨X, hX⟩
  let Y' : DerivedCategory.Plus _ := ⟨Y, hY⟩
  let e'' : H.mapDerivedCategoryPlus.obj X' ≅ H.mapDerivedCategoryPlus.obj Y' :=
    DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimageIso e'
  let hH := (siteComparison_boundedBelow T A).1.some
  let β := DerivedCategory.Plus.ι.mapIso (hH.preimageIso e'')
  refine ⟨β, ?_⟩
  apply R.mapDerivedCategory.map_injective
  have he := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f)
    (hH.map_preimage e''.hom)
  change H.mapDerivedCategory.map β.hom = e'.hom at he
  have hn := c.hom.naturality β.hom
  change H.mapDerivedCategory.map β.hom ≫ (c.app Y).hom =
    (c.app X).hom ≫ R.mapDerivedCategory.map (G.mapDerivedCategory.map β.hom) at hn
  dsimp only [e', Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom] at he
  rw [he] at hn
  apply (cancel_epi (c.app X).hom).1
  simpa [G, Category.assoc, e'] using hn.symm

private theorem etaleComparison_reflects_isGE (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) (a : ℤ)
    (h : ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj X).IsGE a) :
    X.IsGE a := by
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) T
  have : G.Faithful := inferInstance
  apply (DerivedCategory.isGE_iff X a).2
  intro q hq
  exact G.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isGE_iff _ a).1 h q hq)

private theorem compatibleEtaleNormalizations (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : ∀ n : ℕ, PbcWitnessAmbient T d n)
    (hK : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
      ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (K n)))
    (W : ∀ n : ℕ, EtaleOriginWitness T (PbcQuotient d n)
      ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (K n), hK n⟩)
    (θ : ∀ n : ℕ, (pbcWitnessReduction T d n).obj (K (n + 1)) ≅ K n) :
    ∃ β : ∀ n : ℕ,
        (pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj ≅ (W n).L.obj,
      ∀ n : ℕ,
        (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
            (β n).hom ≫ (pbcFixedOriginAlpha T (PbcQuotient d n) (K n) (hK n) (W n)).hom =
          (pbcComparisonReduction T
            (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app (W (n + 1)).L.obj ≫
            (pbcWitnessReduction T d n).map
              (pbcFixedOriginAlpha T (PbcQuotient d (n + 1)) (K (n + 1))
                (hK (n + 1)) (W (n + 1))).hom ≫ (θ n).hom := by
  let α (n : ℕ) := pbcFixedOriginAlpha T (PbcQuotient d n) (K n) (hK n) (W n)
  let e (n : ℕ) :=
    (pbcComparisonReduction T
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).symm.app (W (n + 1)).L.obj ≪≫
      (pbcWitnessReduction T d n).mapIso (α (n + 1)) ≪≫ θ n ≪≫ (α n).symm
  have hsource (n : ℕ) : DerivedCategory.TStructure.t.plus
      ((pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj) := by
    obtain ⟨a, ha⟩ := (W n).L.property
    let G := comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T
    have hge := G.isGE_mapDerivedCategory_obj (W n).L.obj a
    exact ⟨a, etaleComparison_reflects_isGE T (PbcQuotient d n) _ a
      (DerivedCategory.TStructure.t.isGE_of_iso (e n).symm a)⟩
  have lifts (n : ℕ) := etaleComparison_liftIso T (PbcQuotient d n)
    ((pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj) (W n).L.obj
      (hsource n) (W n).L.property (e n)
  choose β hβ using lifts
  refine ⟨β, fun n ↦ ?_⟩
  rw [hβ n]
  simp [α, e, Category.assoc]

private def functionRealizationComparison (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    finiteCoefficientRealization T (PbcQuotient d n) ⋙
        SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).hom ≅
      pbcFunctionRealization T d n := by
  let P := PbcQuotient d n
  let r := AdicCoefficients.finiteRingComparison T P
  have h := pbcAssociatedRestriction_exists T P P
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (Opposite.op n)))
    (finiteCoefficientRingSheaf T P)
    (pbcFunctionScalars T d n) (finiteCoefficientScalarMap T P)
    (RingHom.id P) r.hom (by
      simp [pbcFunctionScalars, r, P]
      rfl)
  exact h.exists.choose.symm

private theorem levelOrigin_realization (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (n : ℕ)
    (h : IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin T d M n) :
    ∃ (K : PbcWitnessAmbient T d n)
      (hK : DerivedCategory.TStructure.t.plus
        ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj K)),
      Nonempty (EtaleOriginWitness T (PbcQuotient d n)
        ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj K, hK⟩) ∧
      Nonempty ((pbcDerivedFunctionRealization T d n).obj K ≅ M.level n) := by
  let : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  let : TopologicalSpace (A ⧸ d.ideal ^ (n + 1)) := ⊥
  let : DiscreteTopology (A ⧸ d.ideal ^ (n + 1)) := discreteTopology_bot _
  obtain ⟨C, hC, ⟨eC⟩⟩ := h
  let R := finiteCoefficientRealization T (PbcQuotient d n)
  let K := R.mapDerivedCategory.asEquivalence.inverse.obj (DerivedCategory.Q.obj C)
  let eR : R.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj C :=
    R.mapDerivedCategory.asEquivalence.counitIso.app _
  obtain ⟨L, hL, ⟨eL⟩⟩ := hC
  obtain ⟨a, b, hab, hbounds⟩ := hL.2
  have hLa : L.IsGE a := (DerivedCategory.isGE_iff L a).2
    (fun i hi ↦ hbounds i (Or.inl hi))
  have himage := (finiteCoefficientComparison T (PbcQuotient d n)).isGE_mapDerivedCategory_obj
    L a
  change ((finiteCoefficientDerivedComparison T (PbcQuotient d n)).obj L).IsGE a at himage
  have : ((finiteCoefficientDerivedComparison T (A ⧸ d.ideal ^ (n + 1))).obj L).IsGE a :=
    himage
  have htarget : (DerivedCategory.Q.obj C).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso eL a
  have hK : DerivedCategory.TStructure.t.plus (R.mapDerivedCategory.obj K) :=
    ⟨a, DerivedCategory.TStructure.t.isGE_of_iso eR.symm a⟩
  let W : EtaleOriginWitness T (PbcQuotient d n)
      ⟨R.mapDerivedCategory.obj K, hK⟩ :=
    { L := ⟨L, ⟨a, hLa⟩⟩
      alpha := DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimageIso
        (eL ≪≫ eR.symm) }
  refine ⟨K, hK, ⟨W⟩, ⟨?_⟩⟩
  let G := SheafOfModules.restrictScalars
    (AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).hom
  let U := SheafOfModules.toSheaf
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (Opposite.op n)))
  have : CategoryTheory.Limits.PreservesFiniteLimits (G ⋙ U) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteLimits
      (SheafOfModules.toSheaf (finiteCoefficientRingSheaf T (PbcQuotient d n))))
  have : CategoryTheory.Limits.PreservesFiniteColimits (G ⋙ U) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteColimits
      (SheafOfModules.toSheaf (finiteCoefficientRingSheaf T (PbcQuotient d n))))
  have : CategoryTheory.Limits.PreservesFiniteLimits G :=
    CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves G U
  have : CategoryTheory.Limits.PreservesFiniteColimits G :=
    CategoryTheory.Limits.preservesFiniteColimits_of_reflects_of_preserves G U
  letI := pbcFunctionRealization_additive T d n
  letI := pbcFunctionRealization_limits T d n
  letI := pbcFunctionRealization_colimits T d n
  let c := CategoryTheory.Functor.mapDerivedCategoryCompIso R G ≪≫
    CategoryTheory.Functor.mapDerivedCategoryNatIso (functionRealizationComparison T d n)
  exact (c.app K).symm ≪≫ G.mapDerivedCategory.mapIso eR ≪≫
    G.mapDerivedCategoryFactors.app C ≪≫ eC

/-- A common intrinsic cohomological interval gives the canonical uniform local
models and compatible bounded-below etale origins. This is the reverse half of the
uniform criterion. -/
theorem pbcUniformReductionCriterion_backward (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcUniformReductionProfile T (pbcIntegralDatum l E) K →
      (PbcHasUniformConstructibleReductions T (pbcIntegralDatum l E) K ∧
        PbcHasCompatibleEtaleOrigins T (pbcIntegralDatum l E) K) := by
  intro hK
  let d := pbcIntegralDatum l E
  let M := pbcReductionAdicTower T d K
  have hlevels := (uniformProfile_localEffectivity T d K hK).1
  have levels (n : ℕ) := levelOrigin_realization T d M n (hlevels n)
  choose V hV W e using levels
  let W' (n : ℕ) := (W n).some
  let e' (n : ℕ) := (e n).some
  let δ (n : ℕ) := (pbcFunctionReduction T d n).symm.app (V (n + 1)) ≪≫
    (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
      (e' (n + 1)) ≪≫ M.normalization (n + 1) n (Nat.le_succ n) ≪≫ (e' n).symm
  let θ (n : ℕ) := (pbcDerivedFunctionRealization T d n).preimageIso (δ n)
  obtain ⟨β, hβ⟩ := compatibleEtaleNormalizations T d V hV W' θ
  let P : PbcWitnessedTower T d :=
    { K := V, boundedBelow := hV, origin := W', theta := θ,
      beta := β, compatibility := hβ }
  refine ⟨uniformProfile_uniformReductions T d K hK, P, e', fun n ↦ ?_⟩
  change (pbcDerivedFunctionRealization T d n).map (θ n).hom ≫ (e' n).hom = _
  change (pbcDerivedFunctionRealization T d n).map
    ((pbcDerivedFunctionRealization T d n).preimage (δ n).hom) ≫ (e' n).hom = _
  rw [Functor.map_preimage]
  dsimp only [δ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Uniform local models with compatible etale origins are equivalent to the
uniform intrinsic cohomology criterion, for the integral coefficient datum. -/
theorem pbcUniformReductionCriterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (PbcHasUniformConstructibleReductions T (pbcIntegralDatum l E) K ∧
      PbcHasCompatibleEtaleOrigins T (pbcIntegralDatum l E) K) ↔
      PbcUniformReductionProfile T (pbcIntegralDatum l E) K := by
  constructor
  · exact pbcUniformLocalModelCohomology l E T K
  · exact pbcUniformReductionCriterion_backward l E T K

end AlgebraicGeometry.Scheme
