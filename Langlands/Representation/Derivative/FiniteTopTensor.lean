import Langlands.Representation.Derivative.TopProduct
import Langlands.Representation.Induction.HeadTailBinaryProduct
import Langlands.Representation.Induction.EmptyProductUnit
import Langlands.Representation.Derivative.ProductVanishing

/-! The entire top derivative of a finite normalized product. -/

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

private def topRankTransportEquiv {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ b b le_rfl).obj
      ((generalLinearRankCast T h).obj A)) ≃ₗ[ℂ]
        ((generalLinearDerivative T ψ a a le_rfl).obj A) := by
  subst b
  exact LinearEquiv.refl ℂ _

private def topEqTransportEquiv {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ b b le_rfl).obj (h ▸ A)) ≃ₗ[ℂ]
      ((generalLinearDerivative T ψ a a le_rfl).obj A) := by
  subst b
  exact LinearEquiv.refl ℂ _

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

private def singletonTopTensorEquiv {n : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = 1)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ≃ₗ[ℂ]
        PiTensorProduct ℂ (fun i =>
          (generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj (σ i)) := by
  letI := T.topology
  let i := B.singleBlockIndex h
  letI : Subsingleton (Fin B.length) :=
    ⟨fun j k => (B.eq_singleBlockIndex h j).trans (B.eq_singleBlockIndex h k).symm⟩
  let A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
    (B.singleBlock_size h i) ▸ σ i
  let τ := fun j => ((B.singleBlock_size h j).symm ▸ A :
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
  let E := Parabolic.equivTrans (T.normalizedProductInductionObjEquiv B τ)
    (T.singleBlockTransportedProductEquiv B h A)
  let eF := (T.normalizedProductInductionFunctor B).mapIso
    (eqToIso (singleFamily_eq T B h σ).symm)
  exact (topMapEquiv T ψ (eF ≪≫ SmoothRep.mkIso E)).trans
    ((topEqTransportEquiv T ψ (B.singleBlock_size h i) (σ i)).trans
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun j =>
        (generalLinearDerivative T ψ (B.size j) (B.size j) le_rfl).obj (σ j)) i).symm)

set_option maxHeartbeats 800000 in
private theorem finiteTopTensor_exists (l : ℕ) :
    ∀ {n : ℕ} (B : GeneralLinear.BlockShape n), B.length = l →
    ∀ (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    letI := T.topology
    Nonempty (((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ≃ₗ[ℂ]
        PiTensorProduct ℂ (fun i =>
          (generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj (σ i))) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro n B hB σ
    let := T.topology
    rcases l with _ | l
    · let : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
      have hn0 : n = 0 := by simpa using B.sum_eq.symm
      subst n
      exact ⟨(T.normalizedProductInductionObjEquiv B σ).toLinearEquiv.trans
        ((T.emptyProductEvaluationEquiv B (fun i => (σ i).representation)).toLinearEquiv.trans
          ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun i => σ i) (Fin B.length)).trans
            (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun i =>
              (generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj (σ i))
              (Fin B.length)).symm))⟩
    rcases l with _ | k
    · exact ⟨singletonTopTensorEquiv T ψ B hB σ⟩
    · rcases B with ⟨r, sizes, positive, sum_eq⟩
      dsimp only at hB
      subst r
      let B : GeneralLinear.BlockShape n := ⟨k + 2, sizes, positive, sum_eq⟩
      obtain ⟨eTail⟩ := ih (k + 1) (by omega) (B.tailShape rfl) rfl
        (fun j => σ (B.tailIndex rfl j))
      let A := σ (B.headIndex rfl)
      let P := (T.normalizedProductInductionFunctor (B.tailShape rfl)).obj
        (fun j => σ (B.tailIndex rfl j))
      exact ⟨(topMapEquiv T ψ (T.headTailBinaryProductIso B rfl σ)).trans
        ((topRankTransportEquiv T ψ (B.headRank_add_tailRank rfl)
          ((T.binaryNormalizedProductFunctor (B.headRank rfl) (B.tailRank rfl)).obj
            (A, P))).trans
          ((topProductTensorEquiv T ψ A P).trans
            ((TensorProduct.congr (LinearEquiv.refl ℂ _) eTail).trans
              (FiniteTensor.headTailLinearEquiv ℂ (fun i : Fin (k + 2) =>
                (generalLinearDerivative T ψ (sizes i) (sizes i) le_rfl).obj (σ i))).symm)))⟩

/-- The entire top derivative of a finite normalized product is the finite
tensor product of the entire top derivatives of its original factors. -/
def finiteProductTopDerivativeTensorEquiv {n : ℕ} (B : GeneralLinear.BlockShape n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ≃ₗ[ℂ]
        PiTensorProduct ℂ (fun i =>
          (generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj (σ i)) :=
  Classical.choice (finiteTopTensor_exists T ψ B.length B rfl σ)

private theorem tensor_nontrivial_iff (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    Nontrivial (V ⊗[ℂ] W) ↔ Nontrivial V ∧ Nontrivial W := by
  constructor
  · intro h
    constructor
    · by_contra hV
      let := not_nontrivial_iff_subsingleton.mp hV
      exact (not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton (V ⊗[ℂ] W))) h
    · by_contra hW
      let := not_nontrivial_iff_subsingleton.mp hW
      exact (not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton (V ⊗[ℂ] W))) h
  · rintro ⟨hV, hW⟩
    exact ProductVanishing.nontrivial_tensor V W

private theorem finiteTensor_nontrivial_iff (r : ℕ) :
    ∀ (V : Fin r → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)],
      Nontrivial (PiTensorProduct ℂ V) ↔ ∀ i, Nontrivial (V i) := by
  induction r with
  | zero =>
    intro V _ _
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      exact (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) (Fin 0)).toEquiv.nontrivial
  | succ r ih =>
    intro V _ _
    rw [Equiv.nontrivial_congr (FiniteTensor.headTailLinearEquiv ℂ V).toEquiv,
      tensor_nontrivial_iff, ih (fun j => V j.succ)]
    constructor
    · rintro ⟨h0, hs⟩ i
      exact Fin.cases h0 hs i
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

/-- A finite product has nonzero entire top derivative exactly when every
original factor does, including the empty-product convention. -/
theorem nontrivial_finiteProductTopDerivative_iff {n : ℕ}
    (B : GeneralLinear.BlockShape n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Nontrivial ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj σ)) ↔
        ∀ i, Nontrivial ((generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj
          (σ i)) := by
  let := T.topology
  exact (Equiv.nontrivial_congr
    (finiteProductTopDerivativeTensorEquiv T ψ B σ).toEquiv).trans
      (finiteTensor_nontrivial_iff B.length _)

end Langlands.Derivative
