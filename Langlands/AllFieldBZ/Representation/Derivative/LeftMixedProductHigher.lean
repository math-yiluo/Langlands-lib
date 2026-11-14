import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductZeroRank
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPsi
import Langlands.AllFieldBZ.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.AllFieldBZ.Representation.Derivative.MixedProductRankCast
import Langlands.AllFieldBZ.Representation.Derivative.OrderRecursion
import Langlands.Representation.Derivative.LeftMixedProductHigher

/-!
# All-field port of `Langlands.Representation.Derivative.LeftMixedProductHigher`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeftMixedProductHigher` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.LeftMixedProductHigher
open Langlands.Derivative.LeftMixedProductHigher hiding derivativeOfOrderTargetTransport leftMixedDerivativeIterateIso leftMixedDerivativeOfOrderIso leftMixedProductDerivativeIso leftPhiStepIso
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility leftCharacter_radical leftCoefficientRadicalProjection leftCoefficientRadicalProjection_surjective leftPhiExpected leftPhiProduct leftPsiBinaryCoefficient leftPsiBinaryCoefficientMap leftPsiBinaryCoefficient_action leftPsiBinaryCoefficient_natural leftPsiCoefficient leftPsiCoefficientEquiv leftPsiCoefficientEquiv_mk_tmul leftPsiCoefficientEquiv_natural leftPsiCoefficientEquiv_section_action leftPsiCoefficientMap leftPsiCoefficientOrdinaryEquiv leftPsiCoefficient_isSmooth leftPsiCoefficient_radical_tmul leftPsiCompatibility leftPsiInductionEquiv leftPsiInductionEquiv_natural leftPsiNormalizedCoefficient leftPsiNormalizedCoefficientMap leftPsiNormalizedCoefficient_action leftPsiPositiveCompactEquiv leftPsiPositiveCompactEquiv_natural leftPsiPositiveEquiv leftPsiPositiveEquiv_natural leftPsiSection_character leftPsiSection_determinantNorm leftPsiSection_halfModulus leftPsiZeroCoefficientEquiv leftPsiZeroCoefficient_isSmooth leftPsiZeroEquiv leftPsiZeroEquiv_natural leftPsiZeroTensorEquiv leftPsiZeroTensorEquiv_natural leftPsi_mirabolic_compactOpenBasis leftPsi_normalSplitEquiv leftPsi_normalSplitEquiv_natural psiMinusOrdinaryEquiv psiMinusOrdinaryEquiv_natural rightPhiProduct rightPhiQuotient rightPhiSubobject
open Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
universe uF uV

variable {F : LocalFieldPackage.{uF}}

theorem derivativeOfOrderTargetTransport (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N n j : ℕ)
    (hN : N = n + j) (hi : 0 < j + 1 ∧ j + 1 ≤ N + 1)
    (e : N + 1 - (j + 1) = n) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF, uV} T ψ N (j + 1) hi ⋙ generalLinearRankCast T e =
      mirabolicRankCast T hN ⋙ mirabolicDerivative T ψ n j := by
  let _ := T.topology
  rw [mirabolicDerivativeOfOrder_eq]
  have aux : ∀ (m l : ℕ) (h : N = m + l) (e' : m = n) (_ : l = j),
      mirabolicRankCast.{uF, uV} T h ⋙ mirabolicDerivative T ψ m l ⋙
          generalLinearRankCast T e' =
        mirabolicRankCast T hN ⋙ mirabolicDerivative T ψ n j := by
    intro m l h e' hl
    subst e' hl
    rw [generalLinearRankCast_refl, Functor.comp_id]
  exact aux (N + 1 - (j + 1)) (j + 1 - 1) (Langlands.Derivative.mirabolic_rank_eq_of_order hi) e (by omega)

def leftPhiStepIso (T : F.TopologicalData)
    (hPhi : Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF, uV} (k + 1) (r + 1) ⋙
        mirabolicRankCast T
          (show (k + 1) + (r + 1) = ((k + 1) + r) + 1 by omega) ⋙
        Mirabolic.phiMinus T ψ ((k + 1) + r) ≅
      (𝟭 _).prod (Mirabolic.phiMinus T ψ r) ⋙
        T.leftMixedProductFunctor (k + 1) r := by
  letI := T.topology
  let e : (k + 1) + r = k + (r + 1) := Nat.succ_add k r
  have hL :
      Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiProduct.{uF, uV} T ψ k (r + 1) ⋙ mirabolicRankCast T e.symm =
        T.leftMixedProductFunctor (k + 1) (r + 1) ⋙
          mirabolicRankCast T
            (show (k + 1) + (r + 1) = ((k + 1) + r) + 1 by omega) ⋙
          Mirabolic.phiMinus T ψ ((k + 1) + r) := by
    simp only [Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiProduct, Functor.assoc]
    rw [← phiMinus_rankCast T ψ e.symm]
    rw [← Functor.assoc (mirabolicRankCast T _) (mirabolicRankCast T _),
      mirabolicRankCast_trans]
  have hR :
      Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiExpected.{uF, uV} T ψ k r ⋙ mirabolicRankCast T e.symm =
        (𝟭 _).prod (Mirabolic.phiMinus T ψ r) ⋙
          T.leftMixedProductFunctor (k + 1) r := by
    simp only [Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiExpected, Functor.assoc, mirabolicRankCast_symm_comp,
      Functor.comp_id]
  exact (eqToIso hL).symm ≪≫
    Functor.isoWhiskerRight (Classical.choice (hPhi ψ k r)) (mirabolicRankCast T e.symm) ≪≫
    eqToIso hR

/-- Target-rank form of the conditional positive-rank derivative comparison. -/
def leftMixedDerivativeIterateIso (T : F.TopologicalData)
    (hPhi : Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k n j : ℕ) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF, uV} (k + 1) (n + j) ⋙
        mirabolicRankCast T
          (show (k + 1) + (n + j) = ((k + 1) + n) + j by omega) ⋙
        mirabolicDerivative T ψ ((k + 1) + n) j ≅
      (𝟭 _).prod (mirabolicDerivative T ψ n j) ⋙
        T.binaryNormalizedProductFunctor (k + 1) n := by
  letI := T.topology
  induction j with
  | zero =>
      simp only [Nat.add_zero, mirabolicRankCast_refl, Functor.id_comp,
        mirabolicDerivative_zero]
      exact Classical.choice (Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCompatibility.{uF, uV} T k n)
  | succ j ih =>
      let e : (k + 1) + (n + j) = ((k + 1) + n) + j := by omega
      have hrec :
          mirabolicRankCast T
              (show (k + 1) + (n + (j + 1)) = ((k + 1) + n) + (j + 1) by omega) ⋙
            mirabolicDerivative T ψ ((k + 1) + n) (j + 1) =
          Mirabolic.phiMinus T ψ ((k + 1) + (n + j)) ⋙
            mirabolicRankCast T e ⋙ mirabolicDerivative T ψ ((k + 1) + n) j := by
        rw [mirabolicDerivative_succ, ← Functor.assoc, phiMinus_rankCast T ψ e,
          Functor.assoc]
      rw [hrec]
      have hp := leftPhiStepIso T hPhi ψ k (n + j)
      simp only [mirabolicRankCast_refl, Functor.id_comp] at hp
      have hfirst := Functor.isoWhiskerRight hp
        (mirabolicRankCast T e ⋙ mirabolicDerivative T ψ ((k + 1) + n) j)
      have hsecond := Functor.isoWhiskerLeft ((𝟭 _).prod (Mirabolic.phiMinus T ψ (n + j))) ih
      have hprod :
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))).prod
              (Mirabolic.phiMinus T ψ (n + j)) ⋙
            (𝟭 _).prod (mirabolicDerivative T ψ n j) ≅
          (𝟭 _).prod
            (Mirabolic.phiMinus T ψ (n + j) ⋙ mirabolicDerivative T ψ n j) :=
        Langlands.Derivative.LeftMixedProductZeroRank.prodCompProdIso _ _ _ _ ≪≫
          NatIso.prod (Functor.leftUnitor _) (Iso.refl _)
      have hthird := Functor.isoWhiskerRight hprod (T.binaryNormalizedProductFunctor (k + 1) n)
      simp only [mirabolicDerivative_succ]
      exact
        (Functor.associator _ _ _).symm ≪≫ hfirst ≪≫
          Functor.associator _ _ _ ≪≫ hsecond ≪≫
          (Functor.associator _ _ _).symm ≪≫ hthird

/-- The exact first-conjunct comparison in positive GL rank, conditional on left Phi. -/
def leftMixedDerivativeOfOrderIso (T : F.TopologicalData)
    (hPhi : Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r i : ℕ)
    (hi : 0 < i ∧ i ≤ r + 1) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF, uV} (k + 1) r ⋙
        mirabolicDerivativeOfOrder T ψ ((k + 1) + r) i ⟨hi.1, by omega⟩ ⋙
          generalLinearRankCast T
            (show (k + 1) + r + 1 - i = (k + 1) + (r + 1 - i) by omega) ≅
      (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
        T.binaryNormalizedProductFunctor (k + 1) (r + 1 - i) := by
  letI := T.topology
  cases i with
  | zero => omega
  | succ j =>
      let n := r + 1 - (j + 1)
      have hr : r = n + j := by dsimp [n]; omega
      let hInput := (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))).prod
        (mirabolicRankCast T hr)
      have hL :
          T.leftMixedProductFunctor.{uF, uV} (k + 1) r ⋙
              mirabolicDerivativeOfOrder T ψ ((k + 1) + r) (j + 1)
                ⟨hi.1, by omega⟩ ⋙
              generalLinearRankCast T
                (show (k + 1) + r + 1 - (j + 1) = (k + 1) + n by dsimp [n]; omega) =
          hInput ⋙
            (T.leftMixedProductFunctor (k + 1) (n + j) ⋙
              mirabolicRankCast T
                (show (k + 1) + (n + j) = ((k + 1) + n) + j by omega) ⋙
              mirabolicDerivative T ψ ((k + 1) + n) j) := by
        rw [derivativeOfOrderTargetTransport T ψ ((k + 1) + r) ((k + 1) + n) j
          (by omega) ⟨hi.1, by omega⟩ (by dsimp [n]; omega)]
        dsimp [hInput]
        rw [← Functor.assoc _ _ (mirabolicRankCast T _ ⋙ mirabolicDerivative T ψ _ j),
          leftMixedProduct_rankCast]
        rw [Functor.assoc, ← Functor.assoc (mirabolicRankCast T _) (mirabolicRankCast T _),
          mirabolicRankCast_trans]
      have hD :
          mirabolicRankCast.{uF, uV} T hr ⋙ mirabolicDerivative T ψ n j =
            mirabolicDerivativeOfOrder T ψ r (j + 1) hi := by
        have h := derivativeOfOrderTargetTransport.{uF, uV} T ψ r n j hr hi
          (show r + 1 - (j + 1) = n from rfl)
        simpa only [generalLinearRankCast_refl, Functor.comp_id] using h.symm
      have hprod :
          hInput ⋙ (𝟭 _).prod (mirabolicDerivative T ψ n j) ≅
            (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r (j + 1) hi) :=
        Langlands.Derivative.LeftMixedProductZeroRank.prodCompProdIso _ _ _ _ ≪≫
          NatIso.prod (Functor.leftUnitor _) (eqToIso hD)
      exact eqToIso hL ≪≫
        Functor.isoWhiskerLeft hInput (leftMixedDerivativeIterateIso T hPhi ψ k n j) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight hprod (T.binaryNormalizedProductFunctor (k + 1) n)

/-- All GL ranks of the first conjunct, with the left Phi premise explicit. -/
theorem leftMixedProductDerivativeIso (T : F.TopologicalData)
    (hPhi : Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T) :
    LeftMixedProductDerivativeIso.{uF, uV} F T := by
  let _ := T.topology
  intro ψ k r i hi
  cases k with
  | zero =>
      exact ⟨LeftMixedProductZeroRank.leftMixedProductZeroRankIso T ψ r i hi⟩
  | succ k =>
      exact ⟨leftMixedDerivativeOfOrderIso T hPhi ψ k r i hi⟩

end Langlands.AllFieldBZ.Derivative.LeftMixedProductHigher
