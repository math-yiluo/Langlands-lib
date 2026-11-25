/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
public import WeilConjectures.CategoryTheory.DeligneLaumon.RationalContinuousCoefficientDerivedLocalization
import all WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Normalized localization of the completed coefficient ring

## References

* Bhatt--Scholze, Lemma 6.8.2, pp. 58--59, and Proposition 6.8.14(2), p. 62
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] pbcIntegralDatum pbcRationalCoefficientEquiv

/-- The completed ring localizes to the rational continuous coefficient ring,
with its specified unit and constant sections. -/
theorem rationalRealizationCoefficientLocalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (R : RationalModuleRealization l E X) :
    let B := pbcAdicCompletion X (pbcIntegralDatum l E)
    let a := pbcCompletedScalarSections X (pbcIntegralDatum l E)
    let t := pbcUniformizer l E
    let S := ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t)
    ∃ c : S ≅ rationalCoefficientSheaf l X E,
      ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t) ≫ c.hom =
        R.integralIso.hom ≫ R.inclusion ∧
      ∀ (r : Localization.Away t) (U : X.ProEtᵒᵖ),
        c.inv.hom.app U
          ((rationalModuleConstantMap l E X).hom.app U
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
                (ULift.up (pbcRationalCoefficientEquiv l E r)))) =
          (scalarLocalizationCoefficientMapOfUniverses (PbcIntegralRing l E)
            B a t r).val U  := by
  classical
  let := coefficientExtensionNormedField l E
  let B := pbcAdicCompletion X (pbcIntegralDatum l E)
  let a := pbcCompletedScalarSections X (pbcIntegralDatum l E)
  let t := pbcUniformizer l E
  have hproj (n : ℕ) :
      pbcCompletedScalar X (pbcIntegralDatum l E) ≫
          pbcAdicProjection X (pbcIntegralDatum l E) n =
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
            (pbcLevelConstantComparison X (pbcIntegralDatum l E) n).hom := by
    dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    exact congrArg (fun f ↦ f ≫ (pbcLevelConstantComparison X (pbcIntegralDatum l E) n).hom)
      ((adicDatumScalar_exists X
        { toCompleteCoefficientDatum := (pbcIntegralDatum l E).toCompleteCoefficientDatum
          quotientFinite := (pbcIntegralDatum l E).quotientFinite }).exists.choose_spec n)
  have hscalar (b : PbcIntegralRing l E) (U : X.ProEtᵒᵖ) :
      R.integralIso.hom.hom.app U ((a b).val U) =
        (show (integralCoefficientSheaf l X E).obj.obj U from
          ContinuousMap.const U.unop.left b) := by
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    obtain ⟨⟨e, he, _⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    have hp : (pbcAdicProjection X (pbcIntegralDatum l E) n).hom.app U ((a b).val U) =
        (pbcFunctionScalars X (pbcIntegralDatum l E) n).app U (Ideal.Quotient.mk _ b) := by
      have hh := congrArg (fun f ↦ f.hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))).app U b))
        (hproj n)
      change _ = _ at hh
      rw [rationalFiniteScalars_constantUnit]
      have hη := congrArg (fun f ↦ f.app U b)
        (toSheafify_naturality (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).map
            (CommRingCat.ofHom (Ideal.Quotient.mk
              ((pbcIntegralDatum l E).ideal ^ (n + 1))))))
      exact hh.trans (congrArg
        ((pbcLevelConstantComparison X (pbcIntegralDatum l E) n).hom.hom.app U) hη.symm)
    have hn := R.integral_normalization n U
      (R.integralIso.hom.hom.app U ((a b).val U)) x
    have hi : R.integralIso.hom ≫
        (R.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
          (R.finiteIso n).hom) =
        pbcAdicProjection X (pbcIntegralDatum l E) n ≫ (R.finiteIso n).hom := by
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hni := congrArg (fun f ↦ f.hom.app U ((a b).val U)) hi
    change (R.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
      (R.finiteIso n).hom).hom.app U (R.integralIso.hom.hom.app U ((a b).val U)) =
      (R.finiteIso n).hom.hom.app U
        ((pbcAdicProjection X (pbcIntegralDatum l E) n).hom.app U ((a b).val U)) at hni
    change (finiteContinuousCoefficientValue l E X n U
      ((R.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (R.finiteIso n).hom).hom.app U
          (R.integralIso.hom.hom.app U ((a b).val U))) x).down = _ at hn
    erw [hni, hp, R.finite_normalization] at hn
    exact hn.symm.trans (congrArg ULift.down
      ((integralCoefficientULift_exists l E n).exists.choose_spec b))
  let P := ringedLocalizationRingPresheafOfUniverses.{u + 1, u + 1, u} B (a t)
  let Q := localizedContinuousMapPresheaf X (PbcIntegralRing l E) t
  let e (U : X.ProEtᵒᵖ) : B.obj.obj U ≃+* C(U.unop.left, PbcIntegralRing l E) :=
    (((sheafToPresheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso
      R.integralIso).app U).commRingCatIsoToRingEquiv
  have he (U : X.ProEtᵒᵖ) :
      (Submonoid.powers (M := B.obj.obj U) ((a t).val U)).map (e U).toMonoidHom =
        Submonoid.powers (ContinuousMap.const U.unop.left t) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (hscalar t U)
  let j (U : X.ProEtᵒᵖ) : Localization.Away (M := B.obj.obj U) ((a t).val U) ≃+*
      Localization.Away (ContinuousMap.const U.unop.left t) :=
    IsLocalization.ringEquivOfRingEquiv
      (Localization.Away (M := B.obj.obj U) ((a t).val U))
      (Localization.Away (ContinuousMap.const U.unop.left t)) (e U) (he U)
  have hj (U : X.ProEtᵒᵖ) (b : B.obj.obj U) :
      j U (algebraMap (B.obj.obj U) (Localization.Away (M := B.obj.obj U) ((a t).val U)) b) =
        algebraMap C(U.unop.left, PbcIntegralRing l E)
          (Localization.Away (ContinuousMap.const U.unop.left t))
          (R.integralIso.hom.hom.app U b) :=
    IsLocalization.ringEquivOfRingEquiv_eq
      (R := B.obj.obj U) (P := C(U.unop.left, PbcIntegralRing l E))
      (S := Localization.Away (M := B.obj.obj U) ((a t).val U))
      (Q := Localization.Away (ContinuousMap.const U.unop.left t)) (he U) b
  let k : P ≅ Q := NatIso.ofComponents (fun U ↦ (j U).toCommRingCatIso) (by
    intro U V f
    apply CommRingCat.hom_ext
    change (j V).toRingHom.comp (ringedSectionLocalizationMapOfUniverses B (a t) f) =
      (localizedContinuousMapRestriction X (PbcIntegralRing l E) t f).comp (j U).toRingHom
    apply IsLocalization.ringHom_ext (R := B.obj.obj U)
      (Submonoid.powers (M := B.obj.obj U) ((a t).val U))
    apply RingHom.ext
    intro b
    change j V (ringedSectionLocalizationMapOfUniverses B (a t) f
      (algebraMap (B.obj.obj U) (Localization.Away (M := B.obj.obj U) ((a t).val U)) b)) =
        localizedContinuousMapRestriction X (PbcIntegralRing l E) t f
          (j U (algebraMap (B.obj.obj U) (Localization.Away (M := B.obj.obj U) ((a t).val U)) b))
    simp only [ringedSectionLocalizationMapOfUniverses, IsLocalization.Away.lift_eq,
      RingHom.comp_apply, hj, localizedContinuousMapRestriction,
      IsLocalization.Away.map, IsLocalization.map_eq]
    exact congrArg (algebraMap _ (Localization.Away (ContinuousMap.const V.unop.left t)))
      (ConcreteCategory.congr_hom (R.integralIso.hom.hom.naturality f) b))
  let c : ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t) ≅
      rationalCoefficientSheaf l X E :=
    (presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso k ≪≫ R.localizationIso
  have hc (U : X.ProEtᵒᵖ) (b : B.obj.obj U) :
      c.hom.hom.app U ((toSheafify (ProEt.topology X) P).app U
        (algebraMap (B.obj.obj U) (Localization.Away (M := B.obj.obj U) ((a t).val U)) b)) =
          R.inclusion.hom.app U (R.integralIso.hom.hom.app U b) := by
    have hk := congrArg (fun f ↦ f.app U (algebraMap (B.obj.obj U)
      (Localization.Away (M := B.obj.obj U) ((a t).val U)) b))
      (toSheafify_naturality (ProEt.topology X) k.hom)
    have hk' : ((presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).map k.hom).hom.app U
        ((toSheafify (ProEt.topology X) P).app U
          (algebraMap (B.obj.obj U) (Localization.Away (M := B.obj.obj U) ((a t).val U)) b)) =
      (toSheafify (ProEt.topology X) Q).app U
        (algebraMap C(U.unop.left, PbcIntegralRing l E)
          (Localization.Away (ContinuousMap.const U.unop.left t))
          (R.integralIso.hom.hom.app U b)) := by
      exact hk.symm.trans (congrArg ((toSheafify (ProEt.topology X) Q).app U) (hj U b))
    refine (congrArg (R.localizationIso.hom.hom.app U) hk').trans ?_
    apply ContinuousMap.ext
    intro x
    apply ULift.down_injective
    exact (R.localization_normalization U (R.integralIso.hom.hom.app U b) x).trans
      (R.inclusion_normalization U.unop (R.integralIso.hom.hom.app U b) x).symm
  refine ⟨c, ?_, ?_⟩
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact hc U b
  · have hconstant (U : X.ProEtᵒᵖ) (b : E) :
        (rationalModuleConstantMap l E X).hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
              (ULift.up b)) =
            (show (rationalCoefficientSheaf l X E).obj.obj U from
              ContinuousMap.const U.unop.left (ULift.up b)) := by
      change ((((sheafificationAdjunction (ProEt.topology X)
        CommRingCat.{u + 1}).homEquiv _ _)
          (rationalModuleConstantMap l E X)).app U) (ULift.up b) = _
      rw [rationalModuleConstantMap, Equiv.apply_symm_apply]
      rfl
    have heq (b : PbcIntegralRing l E) :
        pbcRationalCoefficientEquiv l E (algebraMap _ _ b) = b.down.val := by
      unfold pbcRationalCoefficientEquiv
      rw [RingEquiv.trans_apply]
      erw [IsLocalization.ringEquivOfRingEquiv_eq]
      exact (Padic.coefficientExtension_localization_uniformizer l E).2.choose.commutes b.down
    let S := ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t)
    let q (U : X.ProEtᵒᵖ) : E →+* (rationalCoefficientSheaf l X E).obj.obj U :=
      ((rationalModuleConstantMap l E X).hom.app U).hom.comp
        (((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U).hom.comp
            (ULift.ringEquiv.symm.toRingHom : E →+* ULift.{u + 1} E))
    let b := scalarLocalizationCoefficientMapOfUniverses (PbcIntegralRing l E) B a t
    have hf (U : X.ProEtᵒᵖ) :
        ((c.hom.hom.app U).hom.comp
          (((Pi.evalRingHom (fun V ↦ S.obj.obj V) U).comp
            (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)).subtype).comp b)) =
          (q U).comp (pbcRationalCoefficientEquiv l E).toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers t)
      apply RingHom.ext
      intro z
      change c.hom.hom.app U ((b (algebraMap _ _ z)).val U) =
        q U (pbcRationalCoefficientEquiv l E (algebraMap _ _ z))
      have hb : b (algebraMap _ _ z) =
          (scalarLocalizationSectionsMapOfUniverses
            (ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t))) (a z) :=
        IsLocalization.Away.lift_eq t _ z
      rw [hb, heq]
      change c.hom.hom.app U ((toSheafify (ProEt.topology X) P).app U
        (algebraMap (B.obj.obj U)
          (Localization.Away (M := B.obj.obj U) ((a t).val U)) ((a z).val U))) = _
      rw [hc, hscalar]
      change R.inclusion.hom.app U (ContinuousMap.const U.unop.left z) =
        (rationalModuleConstantMap l E X).hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
              (ULift.up z.down.val))
      rw [hconstant]
      apply ContinuousMap.ext
      intro x
      apply ULift.down_injective
      exact R.inclusion_normalization U.unop (ContinuousMap.const U.unop.left z) x
    intro r U
    have h := DFunLike.congr_fun (hf U) r
    change c.hom.hom.app U ((b r).val U) = q U (pbcRationalCoefficientEquiv l E r) at h
    have hi : c.inv.hom.app U (c.hom.hom.app U ((b r).val U)) = (b r).val U :=
      ConcreteCategory.congr_hom (congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.hom_inv_id) U)
        ((b r).val U)
    exact (congrArg (c.inv.hom.app U) h).symm.trans hi

end AlgebraicGeometry.Scheme
