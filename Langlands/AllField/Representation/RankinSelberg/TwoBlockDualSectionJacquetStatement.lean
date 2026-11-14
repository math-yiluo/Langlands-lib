import Langlands.Representation.RankinSelberg.TwoBlockDualSectionJacquetStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
/-!
# Reversed-dual lower sections and ordinary Jacquet transport

A derived carrier-level formulation of JPSS (1983), Section 4.8 through
(1), printed pages 414–415, using the normalized lower sections of Section 4.6
and the Weyl-translated dual functionals of Section 2.1(3)–(4).
This module states the transport and does not prove it.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockDualSectionJacquetStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

set_option maxHeartbeats 800000 in
/-- One actual inverse-transpose intertwining equivalence between the original
lower induction and the lower induction of the reversed inverse-transpose block
family, with both section evaluation laws, Weyl-corrected scalar realization,
product-Haar change of variables, genuine absolute-integrability equivalences,
and equality of the ordinary Bochner Jacquet functions. The equivalence is
chosen before every character, functional, measure and section input. -/
def TwoBlockDualSectionJacquetStatement.{uF, uW} : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
      letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
      ∀ (W : Fin 2 → Type uW) [hadd : ∀ i, AddCommGroup (W i)]
        [hmod : ∀ i, Module ℂ (W i)]
        (sigma : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
        (∀ i, IsSmooth (sigma i)) →
        let mD : Fin 2 → ℕ := fun i => m i.rev
        let hD : ∑ i, (mD i + 1) = t + 1 :=
          (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
        let WD : Fin 2 → Type uW := fun i => W i.rev
        letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
        letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
        let sigmaD : ∀ i, Representation ℂ (GeneralLinear (mD i + 1) F) (WD i) :=
          fun i => inverseTransposePullback (sigma i.rev)
        let B := succBlockShape m h
        let wB : B.Levi F := fun i => weylLong (m i + 1) F
        let R : PiTensorProduct ℂ W ≃ₗ[ℂ] PiTensorProduct ℂ WD :=
          PiTensorProduct.reindex ℂ W Fin.revPerm
        let T : GeneralLinear (t + 1) F → GeneralLinear (t + 1) F :=
          fun g => weylLong (t + 1) F * inverseTranspose (t + 1) F g
        let rho : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ≃
            Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F :=
          { toFun := fun X i j => -X j.rev i.rev
            invFun := fun Y i j => -Y j.rev i.rev
            left_inv := by intro X; ext i j; simp
            right_inv := by intro Y; ext i j; simp }
        ∃ E : Representation.Equiv
            (inverseTransposePullback (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h sigma))
            (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F hD sigmaD),
          (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma) (g : GeneralLinear (t + 1) F),
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval F hD sigmaD (E f) g =
              R ((B.blockTensor sigma wB) (Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval F h sigma f (T g)))) ∧
          (∀ (fD : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F hD sigmaD)
            (g : GeneralLinear (t + 1) F),
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval F h sigma (E.symm fD) g =
              (B.blockTensor sigma wB)
                (R.symm (Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval F hD sigmaD fD (T g)))) ∧
          ∀ (psi : UnitaryAdditiveCharacter F)
            (ell : ∀ i, glInverseFunctionals psi (m i) (sigma i)),
            let psiD := psi.scale (-1)
            let ellD : ∀ i, glInverseFunctionals psiD (mD i) (sigmaD i) :=
              fun i => secondDualFunctional psi (sigma i.rev) (ell i.rev)
            (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma)
              (g : GeneralLinear (t + 1) F) (z : (succBlockShape mD hD).Levi F),
              Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection (fun i => (ellD i).val) (E f) g z =
                Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection (fun i => (ell i).val) f (T g)
                  (fun i => wB i * inverseTranspose (m i + 1) F
                    (GeneralLinear.reindex
                      (finCongr (congrArg (fun k => m k + 1) (Fin.rev_rev i)))
                      (z i.rev)) * wB i)) ∧
            (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma)
              (g : GeneralLinear (t + 1) F),
              Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection (fun i => (ellD i).val) (E f) g 1 =
                Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection (fun i => (ell i).val) f (T g) 1) ∧
            ∀ (nu : AdditiveHaarMeasure F),
              let mu := rectangularMeasure nu (m 0 + 1) (m 1 + 1)
              let muD := rectangularMeasure nu (m 1 + 1) (m 0 + 1)
              MeasurePreserving rho muD mu ∧
              MeasurePreserving rho.symm mu muD ∧
              (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma)
                (g : GeneralLinear (t + 1) F)
                (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F),
                Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand psiD (fun i => (ellD i).val) (E f) g X =
                  Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand psi (fun i => (ell i).val) f (T g) (rho X)) ∧
              (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma)
                (g : GeneralLinear (t + 1) F),
                Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrableAt psiD (fun i => (ellD i).val) muD (E f) g ↔
                  Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrableAt psi (fun i => (ell i).val) mu f (T g)) ∧
              (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma),
                Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable psiD (fun i => (ellD i).val) muD (E f) ↔
                  Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable psi (fun i => (ell i).val) mu f) ∧
              (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h sigma)
                (g : GeneralLinear (t + 1) F),
                Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction psiD (fun i => (ellD i).val) muD (E f) g =
                  Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction psi (fun i => (ell i).val) mu f (T g))

end Langlands.AllField.RankinSelberg
