import Langlands.Representation.Derivative.TopProduct
import Langlands.Representation.Parabolic.HeadTailProductInduction

/-! Scalar equivalences for top derivatives of finite ordered products. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private def topMapEquiv {r : ℕ}
    {A B : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)}
    (e : letI := T.topology; A ≅ B) :
    letI := T.topology
    ((generalLinearDerivative T ψ r r le_rfl).obj A) ≃ₗ[ℂ]
      ((generalLinearDerivative T ψ r r le_rfl).obj B) :=
  letI := T.topology
  (SmoothRep.equivOfIso ((generalLinearDerivative T ψ r r le_rfl).mapIso e)).toLinearEquiv

private def topTransportLine {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (e : letI := T.topology;
      ((generalLinearDerivative T ψ a a le_rfl).obj A) ≃ₗ[ℂ] ℂ) :
    letI := T.topology
    ((generalLinearDerivative T ψ b b le_rfl).obj (h ▸ A)) ≃ₗ[ℂ] ℂ := by
  subst b
  exact e

private def binaryTopLine {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = n)
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

private theorem transport_symm_cancel {α : Sort*} (P : α → Sort*)
    {a b : α} (h : a = b) (x : P a) : h.symm ▸ (h ▸ x) = x := by
  subst b
  rfl

private theorem singleFamily_eq {n : ℕ} (B : GeneralLinear.BlockShape n)
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

private def singletonTopLine {n : ℕ} (B : GeneralLinear.BlockShape n)
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
private theorem finiteTopLine_exists (l : ℕ) :
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

end Langlands.Derivative
