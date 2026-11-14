import Langlands.Representation.RankinSelberg.FiniteLFactorMultiplicativity
import Langlands.AllField.Representation.RankinSelberg.FiniteGammaMultiplicativity
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
/-!
# Finite-block L-polynomial divisibility from the two-block input

Internal finite induction on the ordered block family. The two-block analytic
input remains an explicit hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaMultiplicativityStatement TwoBlockLFactorMultiplicativityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue finiteFunctionMellin finiteFunctionShellSeries gammaMultiplicativity_of_twoBlock hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lFactorMultiplicativity_of_twoBlock lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductRankCastEquiv normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleBlock_L_iff singleBlock_gamma_iff singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable succSingleBlockNormalizedProductEquiv symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerTypeLPolynomial whittakerTypeLPolynomial_spec zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement UnipotentOrbitStatement compactLocalization exists_compactOpen_glCoefficientRightStabilizer functionalsCongr inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV uW

section PolynomialChoice

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (GeneralLinear (n + 1) F) W)
  (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
  (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)

/-- The symmetric L-polynomial chosen from closed full Whittaker-type existence. -/
def whittakerTypeLPolynomial : ℂ[X] :=
  Classical.choose (symmetricLPolynomialExists F ψ ν r n V W π σ hπ hσ)

/-- The chosen polynomial certifies the pair at every compatible quotient measure. -/
theorem whittakerTypeLPolynomial_spec :
    IsPadicSymmetricLPolynomial F ψ ν.val π σ
      (whittakerTypeLPolynomial F ψ ν π σ hπ hσ) :=
  Classical.choose_spec (symmetricLPolynomialExists F ψ ν r n V W π σ hπ hσ)

end PolynomialChoice

private theorem twoBlockL_on_shape
    (hTwo : TwoBlockLFactorMultiplicativityStatement.{uF,uV,uW})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (size : Fin 2 → ℕ) (pos : ∀ i, 0 < size i)
    (total : ∑ i, size i = t + 1) (m : Fin 2 → ℕ)
    (hs : size = fun i => m i + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (GeneralLinear (size i) F) (W i))
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
        (rankCastRepresentation (congrFun hs i) (σ i))) :
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced ⟨2, size, pos, total⟩ σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π
        (rankCastRepresentation (congrFun hs i) (σ i)) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P := by
  subst size
  exact hTwo F ψ ν r t m total π σ hπ hσ

set_option maxHeartbeats 800000 in
/-- Ordered finite-block L-polynomial existence and divisibility, conditional
only on two-block multiplicativity at the induced factor-carrier universe. -/
theorem lFactorMultiplicativity_of_twoBlock
    (hTwo : TwoBlockLFactorMultiplicativityStatement.{uF,uV,max uF uW}) :
    LFactorMultiplicativityStatement.{uF,uV,uW} := by
  intro F _ _ _ _ ψ ν r t k m h V _ _ W _ _ π σ hπ hσ
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  induction k generalizing t with
  | zero =>
      simp at h
  | succ k ih =>
      cases k with
      | zero =>
          let P := whittakerTypeLPolynomial F ψ ν π (σ 0) hπ (hσ 0)
          have hP := whittakerTypeLPolynomial_spec F ψ ν π (σ 0) hπ (hσ 0)
          refine ⟨P, fun _ => P, ?_, ?_, 1, 0, ?_⟩
          · exact (singleBlock_L_iff F m σ π h (fun i => (hσ i).1.1)).mpr hP
          · intro i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            exact hP
          · simp
      | succ k =>
          let B := succBlockShape m h
          let tailM : Fin (k + 1) → ℕ := fun j => m j.succ
          have hpos : 0 < ∑ j : Fin (k + 1), (tailM j + 1) := by
            apply Finset.sum_pos
            · intro j _
              exact Nat.succ_pos _
            · exact Finset.univ_nonempty
          obtain ⟨s, hs⟩ : ∃ s, (∑ j : Fin (k + 1), (tailM j + 1)) = s + 1 :=
            ⟨(∑ j : Fin (k + 1), (tailM j + 1)) - 1, by omega⟩
          let tailσ := fun j : Fin (k + 1) => σ j.succ
          obtain ⟨Pt, Pit, hPt, hPit, Qt, etail, htailRelation⟩ :=
            ih s tailM hs (W := fun j => W j.succ) tailσ (fun j => hσ j.succ)
          have htype := normalizedProductWhittakerType F ψ s (k + 1) tailM hs
            tailσ (fun j => hσ j.succ)
          let bundled := fun i => SmoothRep.of (σ i) (hσ i).1.1
          let outer := T.headTailProductFactors B rfl bundled
          let C := B.headTailShape rfl
          let outerM : Fin 2 → ℕ := Fin.cases (m 0) (fun _ => s)
          have hsize : C.size = fun i => outerM i + 1 := by
            funext i
            fin_cases i
            · rfl
            · exact hs
          let et := normalizedProductRankCastEquiv T (B.tailShape rfl) hs tailσ
          have houter : ∀ i, IsOfWhittakerType (outerM i) (standardCharacter ψ (outerM i))
              (rankCastRepresentation (congrFun hsize i) (outer i).representation) := by
            intro i
            fin_cases i
            · exact (hσ 0).of_equiv (universeLiftEquiv.{uF} (σ 0))
            · exact htype.of_equiv et.symm
          obtain ⟨P, H, hP, hH, Qo, eouter, houterRelation⟩ :=
            twoBlockL_on_shape hTwo F ψ ν r t C.size C.positive C.sum_eq
              outerM hsize π (fun i => (outer i).representation) hπ houter
          have hhead : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) (H 0) :=
            (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl π)
              (universeLiftEquiv.{uF} (σ 0))).mpr (hH 0)
          have htail : H 1 = Pt :=
            ((Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl π) et).mp
              (hH 1)).unique hPt
          refine ⟨P, Fin.cons (H 0) Pit, ?_, ?_, Qo * Qt, etail + eouter, ?_⟩
          · exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv
              (Representation.Equiv.refl π)
              (T.headTailProductInductionEquiv B rfl bundled)).mpr hP
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact hhead
            · exact hPit j
          · have hinner : X ^ etail * (H 0 * ∏ j, Pit j) = Qt * (H 0 * Pt) := by
              calc
                X ^ etail * (H 0 * ∏ j, Pit j) = H 0 * (X ^ etail * ∏ j, Pit j) := by
                  ring
                _ = H 0 * (Qt * Pt) := by rw [htailRelation]
                _ = Qt * (H 0 * Pt) := by ring
            have hout : X ^ eouter * (H 0 * Pt) = Qo * P := by
              simpa only [Fin.prod_univ_two, htail] using houterRelation
            calc
              X ^ (etail + eouter) * ∏ i, Fin.cons (H 0) Pit i =
                  X ^ eouter * (X ^ etail * (H 0 * ∏ j, Pit j)) := by
                rw [Fin.prod_univ_succ]
                simp only [Fin.cons_zero, Fin.cons_succ]
                rw [pow_add]
                ring
              _ = X ^ eouter * (Qt * (H 0 * Pt)) := by rw [hinner]
              _ = Qt * (X ^ eouter * (H 0 * Pt)) := by ring
              _ = Qt * (Qo * P) := by rw [hout]
              _ = Qo * Qt * P := by ring

end Langlands.AllField.RankinSelberg
