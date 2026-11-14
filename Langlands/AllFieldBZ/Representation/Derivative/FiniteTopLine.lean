import Langlands.AllFieldBZ.Representation.Derivative.TopProduct
import Langlands.AllFieldBZ.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Derivative.FiniteTopLine

/-!
# All-field port of `Langlands.Representation.Derivative.FiniteTopLine`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.FiniteTopLine` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso finiteProductTopDerivativeLineEquiv generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero topProductIso topProductTensorEquiv
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private def _root_.Langlands.Derivative.topMapEquiv {r : ℕ}
    {A B : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)}
    (e : letI := T.topology; A ≅ B) :
    letI := T.topology
    ((generalLinearDerivative T ψ r r le_rfl).obj A) ≃ₗ[ℂ]
      ((generalLinearDerivative T ψ r r le_rfl).obj B) :=
  letI := T.topology
  (SmoothRep.equivOfIso ((generalLinearDerivative T ψ r r le_rfl).mapIso e)).toLinearEquiv

private def _root_.Langlands.Derivative.topTransportLine {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (e : letI := T.topology;
      ((generalLinearDerivative T ψ a a le_rfl).obj A) ≃ₗ[ℂ] ℂ) :
    letI := T.topology
    ((generalLinearDerivative T ψ b b le_rfl).obj (h ▸ A)) ≃ₗ[ℂ] ℂ := by
  subst b
  exact e

private def _root_.Langlands.Derivative.binaryTopLine {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = n)
    (A : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
    (eA : letI := T.topology;
      ((generalLinearDerivative T ψ a a le_rfl).obj A) ≃ₗ[ℂ] ℂ)
    (eB : letI := T.topology;
      ((generalLinearDerivative T ψ b b le_rfl).obj B) ≃ₗ[ℂ] ℂ) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor
        ((GeneralLinear.BlockShape.binary a b ha hb).rankCast h)).obj
        (Fin.cases A (fun _ => B)))) ≃ₗ[ℂ] ℂ := by
  subst n
  letI := T.topology
  have hf : (T.binaryPairFamilyFunctor ha hb).obj (A,B) =
      Fin.cases A (fun _ => B) := by
    funext i
    fin_cases i <;> rfl
  let eF := (T.normalizedProductInductionFunctor
    (GeneralLinear.BlockShape.binary a b ha hb)).mapIso (eqToIso hf.symm)
  let E := ((T.binaryNormalizedProductPositiveIso ha hb).app (A,B)).symm
  exact (topMapEquiv T ψ (eF ≪≫ E)).trans
    ((topProductTensorEquiv T ψ A B).trans
      ((TensorProduct.congr eA eB).trans (TensorProduct.lid ℂ ℂ)))

private theorem _root_.Langlands.Derivative.transport_symm_cancel {α : Sort*} (P : α → Sort*)
    {a b : α} (h : a = b) (x : P a) : h.symm ▸ (h ▸ x) = x := by
  subst b
  rfl

private theorem _root_.Langlands.Derivative.singleFamily_eq {n : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = 1)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun j => ((B.singleBlock_size h j).symm ▸
      ((B.singleBlock_size h (B.singleBlockIndex h)) ▸ σ (B.singleBlockIndex h)) :
        SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))) = σ := by
  let := T.topology
  funext j
  have hj := B.eq_singleBlockIndex h j
  subst j
  exact transport_symm_cancel
    (fun r => SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)) _ _

private def _root_.Langlands.Derivative.singletonTopLine {n : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = 1)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (e : letI := T.topology;
      ∀ i, ((generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj
        (σ i)) ≃ₗ[ℂ] ℂ) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  let i := B.singleBlockIndex h
  let A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
    (B.singleBlock_size h i) ▸ σ i
  let τ := fun j => ((B.singleBlock_size h j).symm ▸ A :
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
  let E := Parabolic.equivTrans (T.normalizedProductInductionObjEquiv B τ)
    (T.singleBlockTransportedProductEquiv B h A)
  let eF := (T.normalizedProductInductionFunctor B).mapIso
    (eqToIso (singleFamily_eq T B h σ).symm)
  exact (topMapEquiv T ψ (eF ≪≫ SmoothRep.mkIso E)).trans
    (topTransportLine T ψ (B.singleBlock_size h i) (σ i) (e i))

set_option maxHeartbeats 800000 in
private theorem _root_.Langlands.Derivative.finiteTopLine_exists (l : ℕ) :
    ∀ {n : ℕ}, 0 < n → ∀ (B : GeneralLinear.BlockShape n), B.length = l →
    ∀ (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (letI := T.topology;
      ∀ i, ((generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj
        (σ i)) ≃ₗ[ℂ] ℂ) →
    letI := T.topology
    Nonempty (((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ≃ₗ[ℂ] ℂ) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro n hn B hB σ e
    let := T.topology
    rcases l with _ | l
    · have hempty : IsEmpty (Fin B.length) :=
        ⟨fun i => by have := i.isLt; omega⟩
      have hn0 : n = 0 := by simpa using B.sum_eq.symm
      omega
    rcases l with _ | k
    · exact ⟨singletonTopLine T ψ B hB σ e⟩
    · have h : B.length = k + 2 := hB
      obtain ⟨eTail⟩ := ih (k + 1) (by omega) (B.tailRank_pos h)
        (B.tailShape h) rfl (fun j => σ (B.tailIndex h j))
        (fun j => e (B.tailIndex h j))
      let A : SmoothRep.{0,uF,max uF uV} ℂ
          (GeneralLinear (B.headRank h) F.Carrier) :=
        SmoothRep.universeLift.{uF} (σ (B.headIndex h))
      let P : SmoothRep.{0,uF,max uF uV} ℂ
          (GeneralLinear (B.tailRank h) F.Carrier) :=
        (T.normalizedProductInductionFunctor (B.tailShape h)).obj
          (fun j => σ (B.tailIndex h j))
      let eHead : ((generalLinearDerivative T ψ (B.headRank h) (B.headRank h)
          le_rfl).obj A) ≃ₗ[ℂ] ℂ := (topMapEquiv T ψ
        (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF}
          (σ (B.headIndex h))).symm)).trans (e (B.headIndex h))
      have hf : T.headTailProductFactors B h σ = Fin.cases A (fun _ => P) := by
        funext i
        fin_cases i <;> rfl
      let E := T.headTailProductInductionIso B h σ ≪≫
        (T.normalizedProductInductionFunctor (B.headTailShape h)).mapIso
          (eqToIso hf)
      let eBin := binaryTopLine T ψ
        (a := B.headRank h) (b := B.tailRank h) (n := n)
        (B.headRank_pos h) (B.tailRank_pos h)
        (B.headRank_add_tailRank h) A P eHead eTail
      exact ⟨(topMapEquiv T ψ E).trans eBin⟩

/-- Scalar top-derivative data for the entire finite ordered product. -/
def finiteProductTopDerivativeLineEquiv {n : ℕ} (hn : 0 < n)
    (B : GeneralLinear.BlockShape n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (e : letI := T.topology;
      ∀ i, ((generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj
        (σ i)) ≃ₗ[ℂ] ℂ) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ≃ₗ[ℂ] ℂ :=
  Classical.choice (finiteTopLine_exists T ψ B.length hn B rfl σ e)

end Langlands.AllFieldBZ.Derivative
