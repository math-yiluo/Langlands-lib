/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Descent of the fixed integral scalar comparison

Source: trace-definition coefficient-category sentence, raw localization steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

open scoped TensorProduct

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

attribute [local irreducible] HasDerivedCategory.standard
  FdOrdinaryScalarTransport.complex FdOrdinaryScalarTransport.completion
  fdCoefficientTransportFactors pbcIntegralDatum completedAdicChangeData
  integralDetailedCoefficientComparison sfRationalTriangulationDatum
  sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.transition
  pbcScalarCommShift pbcRationalHasShift
  ScalarLocalization.composition ScalarLocalization.category

private theorem stageFactors (E : Padic.FiniteCoefficientFields l Ω) :
    sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T ⋙
        suppliedJ l Ω T stage E =
      I l Ω T stage E ⋙ pbcStageLocalization l Ω T E := by
  apply Functor.hext (fun K ↦ (stage E).objects ⟨K⟩)
  intro K H f
  have h := (stage E).tensors K H 1 f
  simp only [fdRawTensor, map_one] at h
  dsimp only [suppliedJ, I, sfRationalConstructibleLocalization,
    pbcStageLocalization, ScalarLocalization.localization, Functor.comp_map] at *
  with_unfolding_all exact h

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem scalarFactors {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T ⋙
        sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E) T 0
          (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) =
      U l Ω T h ⋙ sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω L) T := by
  apply Functor.hext
    (fun K ↦ sfRationalScalarExtension_obj l (pbcFiniteField.{u} l Ω E) T 0
      (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) ⟨K⟩)
  intro K H f
  have h := sfRationalScalarExtension_map_tmul l (pbcFiniteField.{u} l Ω E) T 0
    (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) K H f 1
  simp only [map_one] at h
  dsimp only [AlgebraicallyClosedCoefficients.coefficientInclusion,
    AlgebraicallyClosedCoefficients.Coefficient,
    pbcFiniteField, pbcFiniteFieldField, pbcFiniteFieldAlgebra, pbcFiniteFieldInclusion,
    sfRationalConstructibleLocalization, ScalarLocalization.localization,
    Functor.comp_map, U] at *
  with_unfolding_all exact h

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem sfLocalization_isLocalization (E : Padic.FiniteCoefficientFields l Ω) :
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).IsLocalization
      (Rationalization.W
        (Submonoid.powers (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)))
        (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  have : ∀ n : ℤ,
      (shiftFunctor (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) n).Linear
        (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)) :=
    ScalarLocalization.semilinear_all_shift_linear _ _
  exact ScalarLocalization.semilinear_localization_isLocalization _ _ _

private def rawIsoOriginal {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (b : I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L) :
    sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E) T 0
        (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) ⋙ suppliedJ l Ω T stage L ≅
      suppliedJ l Ω T stage E ⋙ (P l Ω T).T h := by
  let Q := sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T
  let QL := sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω L) T
  let PL := pbcStageLocalization l Ω T L
  let S := sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E) T 0
    (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h)
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)))
    (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
  have : Q.IsLocalization W := sfLocalization_isLocalization l Ω T E
  let e : Q ⋙ (S ⋙ suppliedJ l Ω T stage L) ≅
      Q ⋙ (suppliedJ l Ω T stage E ⋙ (P l Ω T).T h) :=
    (Functor.associator Q S _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (scalarFactors l Ω T h)) _ ≪≫
      Functor.associator _ QL _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (stageFactors l Ω T stage L)) ≪≫
      (Functor.associator _ _ PL).symm ≪≫
      Functor.isoWhiskerRight b.symm PL ≪≫
      Functor.associator _ _ PL ≪≫
      Functor.isoWhiskerLeft _ (pbcScalarIntegralComparison l Ω T dT.out iT.out h).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (stageFactors l Ω T stage E)).symm _ ≪≫
      Functor.associator _ _ _
  exact Localization.liftNatIso Q W _ _ _ _ e

private theorem rawIsoOriginal_app {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (b : I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    HEq ((rawIsoOriginal l Ω T stage h b).hom.app
      ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K))
      ((pbcStageLocalization l Ω T L).map (b.inv.app K) ≫
        (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
          ((I l Ω T stage E).obj K)) := by
  dsimp only [rawIsoOriginal]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToIso.inv, eqToHom_app]
  simp only [eqToHom_map]
  apply (eqToHom_comp_heq _ _).trans
  apply (eqToHom_comp_heq _ _).trans
  rw [← Category.assoc]
  exact comp_eqToHom_heq _ _

/-- Localize the inverse integral scalar comparison before coefficient-presentation transport.
Source: assigned raw scalar-descent proof, first step
(blueprint: lem-fd-raw-localized-comparison-exists).

Proof: The stage tensor formula at scalar one identifies Q followed by the supplied
rational functor with I followed by the PBC localization. The scalar tensor formula
at one identifies Q followed by rational scalar extension with U followed by Q.
Whisker the inverse of b by the final localization and compose with these
identifications and the inverse ordinary-scalar comparison. The source Q is a
localization, so lift this natural isomorphism with Localization.liftNatIso.
Its integral component formula cancels the identity associators and equality
transports, giving exactly the two arrows below. This constructs the isomorphism
and its naturality and inverse equations; no shift or coherence assertion is used. -/
theorem rawLocalizedComparisonExists {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (b : I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L) :
    ∃ e : sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E) T 0
        (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) ⋙ suppliedJ l Ω T stage L ≅
      suppliedJ l Ω T stage E ⋙ (P l Ω T).T h,
      ∀ K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T,
        HEq (e.hom.app
          ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K))
          ((pbcStageLocalization l Ω T L).map (b.inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K)) := by
  exact ⟨rawIsoOriginal l Ω T stage h b, rawIsoOriginal_app l Ω T stage h b⟩

end WeilConjectures.FdRawLocalization
