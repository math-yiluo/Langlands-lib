import Langlands.Representation.RankinSelberg.FiniteGammaMultiplicativity
import Langlands.AllField.Representation.Parabolic.HeadTailProductInduction
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.SingleBlockFactors
import Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
/-! Finite-block gamma multiplicativity from the two-block analytic input. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockGammaMultiplicativityStatement TwoBlockLFactorMultiplicativityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement gammaMultiplicativity_of_twoBlock isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductRankCastEquiv normalizedProductWhittakerType singleBlock_L_iff singleBlock_gamma_iff succSingleBlockNormalizedProductEquiv
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement UnipotentOrbitStatement compactLocalization functionalsCongr inducedLocalization_of_prerequisites unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV uW

/-- Normalized product induction commutes with substitution of the total rank. -/
def normalizedProductRankCastEquiv
    {F : Type uF} [Field F] (T : LocalFieldData F)
    {a b : ℕ} (C : BlockShape a) (h : a = b)
    {W : Fin C.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (C.size i) F) (W i)) :
    (rankCastRepresentation h (T.normalizedProductInduced C σ)).Equiv
      (T.normalizedProductInduced (C.rankCast h) σ) := by
  subst b
  exact Representation.Equiv.refl _

private theorem twoBlockGamma_on_shape
    (hTwo : TwoBlockGammaMultiplicativityStatement.{uF,uV,uW})
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
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π
        (rankCastRepresentation (congrFun hs i) (σ i)) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced ⟨2, size, pos, total⟩ σ) (∏ i, G i) := by
  subst size
  exact hTwo F ψ ν r t m total π σ hπ hσ

private theorem exists_gamma_of_twoBlock
    (hTwo : TwoBlockGammaMultiplicativityStatement.{uF,uV,uW})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r s : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (GeneralLinear (s + 1) F) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType s (standardCharacter ψ s) σ) :
    ∃ G, IsPadicSymmetricGammaFactor F ψ ν.val π σ G := by
  have h : ∑ i : Fin 2, ((fun _ => s) i + 1) = (s + s + 1) + 1 := by
    simp only [Fin.sum_univ_two]
    omega
  obtain ⟨G, hG, _⟩ := hTwo F ψ ν r (s + s + 1) (fun _ => s) h
    π (fun _ => σ) hπ (fun _ => hσ)
  exact ⟨G 0, hG 0⟩

set_option maxHeartbeats 800000 in
/-- Finite induction on the ordered block family, retaining the two analytic
inputs at the original and induced carrier universes. -/
theorem gammaMultiplicativity_of_twoBlock
    (hTwo : TwoBlockGammaMultiplicativityStatement.{uF,uV,uW})
    (hTwoLift : TwoBlockGammaMultiplicativityStatement.{uF,uV,max uF uW}) :
    GammaMultiplicativityStatement.{uF,uV,uW} := by
  intro F _ _ _ _ ψ ν r t k m h V _ _ W _ _ π σ hπ hσ
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  induction k generalizing t with
  | zero =>
      simp at h
  | succ k ih =>
      cases k with
      | zero =>
          obtain ⟨G, hG⟩ := exists_gamma_of_twoBlock hTwo F ψ ν r (m 0) π (σ 0) hπ (hσ 0)
          refine ⟨fun _ => G, fun i => ?_, ?_⟩
          · have hi : i = 0 := Fin.eq_zero i
            subst i
            exact hG
          · simpa using (singleBlock_gamma_iff F m σ π h (fun i => (hσ i).1.1)).mpr hG
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
          obtain ⟨Gt, hGt, hIt⟩ := ih s tailM hs (W := fun j => W j.succ)
            tailσ (fun j => hσ j.succ)
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
          obtain ⟨H, hH, hI⟩ := twoBlockGamma_on_shape hTwoLift F ψ ν r t C.size
            C.positive C.sum_eq outerM hsize π (fun i => (outer i).representation) hπ houter
          have hhead : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0) (H 0) :=
            (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π)
              (universeLiftEquiv.{uF} (σ 0))).mpr (hH 0)
          have htail : H 1 = ∏ j, Gt j :=
            ((Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π) et).mp
              (hH 1)).unique hIt
          refine ⟨Fin.cons (H 0) Gt, ?_, ?_⟩
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact hhead
            · exact hGt j
          · have hprod : (∏ i : Fin 2, H i) =
                ∏ i : Fin (k + 2), Fin.cons (H 0) Gt i := by
              rw [Fin.prod_univ_two, Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [htail]
            rw [← hprod]
            exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
              (Representation.Equiv.refl π)
              (T.headTailProductInductionEquiv B rfl bundled)).mpr hI

end Langlands.AllField.RankinSelberg
