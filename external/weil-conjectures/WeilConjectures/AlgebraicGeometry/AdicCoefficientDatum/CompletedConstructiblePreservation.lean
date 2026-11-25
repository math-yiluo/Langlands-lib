/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.Completed.CompletedConstructibleReductionControl
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedConstructibleTowerLocalEffectivity
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedEtaleOriginWitnesses
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback

/-! # Constructible preservation with the original adic coefficient datum

The coefficient ring has the same universe as the module sheaves, with no lift or
replacement of the datum. Source: Stacks 09C7 and 09C2; blueprint preservation proposition.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem datumPush_eq_actualPush
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    d.push f = pbcActualDerivedPush f d := by
  have hm : proEtaleRingModuleDirectImage f (d.completedRing T) (d.completedRing S)
      (d.integralRingIso f) = completedModuleDirectImage f d := by
    unfold proEtaleRingModuleDirectImage completedModuleDirectImage
    unfold proEtaleRingDirectImageMap completedCoefficientDirectImageMap
    rw [cbcDatumCoefficient_eq]
    rfl
  cases hm
  rfl

private theorem boundedBelow_of_exact_faithful
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : DerivedCategory C)
    (hK : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj K)) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, ha⟩ := hK
  refine ⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩
  intro i hi
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isGE_iff _ a).1 ha i hi)

private theorem compatibleOrigins_of_levelwise
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d)
    (M : ∀ n : ℕ, ProEtale.PbcWitnessAmbient T d n)
    (hM : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
      ((ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj
        (M n)))
    (W : ∀ n : ℕ, EtaleOriginWitness T (ProEtale.PbcQuotient d n)
      ⟨(ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj
        (M n), hM n⟩)
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (M n) ≅
      (pbcCompletedReduction T d n).obj K) : PbcHasCompatibleEtaleOrigins T d K := by
  classical
  let theta (n : ℕ) : (ProEtale.pbcWitnessReduction T d n).obj (M (n + 1)) ≅ M n :=
    (pbcDerivedFunctionRealization T d n).preimageIso
      ((pbcFunctionReduction T d n).symm.app (M (n + 1)) ≪≫
        (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
          (e (n + 1)) ≪≫
        pbcReductionNormalization (pbcAdicProjection T d (n + 1))
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
          (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K ≪≫ (e n).symm)
  have lift (n : ℕ) :
      ∃ beta : (ProEtale.pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj ≅
          (W n).L.obj,
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T).mapDerivedCategory.map beta.hom ≫
            (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d n)
              (M n) (hM n) (W n)).hom =
          (ProEtale.pbcComparisonReduction T
            (ProEtale.pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
              (W (n + 1)).L.obj ≫
            (ProEtale.pbcWitnessReduction T d n).map
              (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d (n + 1))
                (M (n + 1)) (hM (n + 1)) (W (n + 1))).hom ≫ (theta n).hom := by
    let C := (ProEtale.pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj
    let F := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T).mapDerivedCategory
    let a : F.obj C ≅ M n :=
      (ProEtale.pbcComparisonReduction T
        (ProEtale.pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).symm.app
          (W (n + 1)).L.obj ≪≫
        (ProEtale.pbcWitnessReduction T d n).mapIso
          (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d (n + 1))
            (M (n + 1)) (hM (n + 1)) (W (n + 1))) ≪≫ theta n
    have hC : DerivedCategory.TStructure.t.plus C := by
      apply boundedBelow_of_exact_faithful (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T)
      apply boundedBelow_of_exact_faithful
        (ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n))
      exact DerivedCategory.TStructure.t.plus.prop_of_iso
        ((ProEtale.finiteCoefficientRealization T
          (ProEtale.PbcQuotient d n)).mapDerivedCategory.mapIso a).symm (hM n)
    let b : F.obj C ≅ F.obj (W n).L.obj :=
      a ≪≫ (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d n)
        (M n) (hM n) (W n)).symm
    obtain ⟨f, hf⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C (W n).L.obj
        (W n).L.property).2 b.hom
    obtain ⟨g, hg⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map (W n).L.obj C hC).2 b.inv
    change F.map f = b.hom at hf
    change F.map g = b.inv at hg
    have hfg : f ≫ g = 𝟙 C :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C C hC).1 (by
        change F.map (f ≫ g) = F.map (𝟙 C)
        simp only [Functor.map_comp, hf, hg, Iso.hom_inv_id]
        exact (F.map_id _).symm)
    have hgf : g ≫ f = 𝟙 (W n).L.obj :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (W n).L.property).1 (by
        change F.map (g ≫ f) = F.map (𝟙 (W n).L.obj)
        simp only [Functor.map_comp, hf, hg, Iso.inv_hom_id]
        exact (F.map_id _).symm)
    refine ⟨⟨f, g, hfg, hgf⟩, ?_⟩
    change F.map f ≫ _ = _
    rw [hf]
    simp [b, a, Category.assoc]
  choose beta hbeta using lift
  refine ⟨⟨M, hM, W, theta, beta, hbeta⟩, e, ?_⟩
  intro n
  have ht := Functor.map_preimage
    (pbcDerivedFunctionRealization T d n)
    (((pbcFunctionReduction T d n).symm.app (M (n + 1)) ≪≫
        (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
          (e (n + 1)) ≪≫
        pbcReductionNormalization (pbcAdicProjection T d (n + 1))
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
          (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K ≪≫ (e n).symm).hom)
  change (pbcDerivedFunctionRealization T d n).map (theta n).hom ≫ _ = _
  rw [show (pbcDerivedFunctionRealization T d n).map (theta n).hom = _ from ht]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rfl

private def fixedRestrictId (T : Scheme.{u}) (P : Type (u + 1)) [CommRing P] :
    Sheaf.restrictScalars (ProEt.topology T) (RingHom.id P) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId P) ≪≫ F.obj.rightUnitor))
    (by intro F G f; ext U x; rfl)

private def functionRealizationComparison
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) :
    pbcFunctionRealization T d n ≅
      ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n) ⋙
        SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison T (ProEtale.PbcQuotient d n)).hom := by
  let P := ProEtale.PbcQuotient d n
  let e := AdicCoefficients.finiteRingComparison T P
  let a := pbcAssociatedRestriction_exists T P P
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (Opposite.op n)))
    (ProEtale.finiteCoefficientRingSheaf T P)
    (pbcFunctionScalars T d n) (ProEtale.finiteCoefficientScalarMap T P)
    (RingHom.id P) e.hom (by
      simp [pbcFunctionScalars, P, e]
      rfl)
  exact (Functor.isoWhiskerRight (fixedRestrictId T P).symm
    (pbcFunctionRealization T d n)) ≪≫ a.exists.choose

end AlgebraicGeometry.Scheme
