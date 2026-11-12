import Langlands.Representation.Classification.Segments
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.NormalizedProductCharacterTwist

/-! Common real determinant twists of the literal binary product in all ranks. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.PadicField.TopologicalData

open CategoryTheory Langlands.GeneralLinear
open scoped TensorProduct

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem determinantPowerCharacter_reindex {a b : ℕ} (h : a = b)
    (s : ℝ) (g : GeneralLinear a F.Carrier) :
    T.determinantPowerCharacter b s
        (GeneralLinear.reindex (R := F.Carrier) (finCongr h) g) =
      T.determinantPowerCharacter a s g := by
  subst b
  rw [GeneralLinear.reindex_finCongr_rfl]
  rfl

variable {a b : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (s : ℝ)

private def binaryLeftZeroRealTwistIso (ha : a = 0) :
    letI := T.topology
    T.segmentFactor ((T.binaryNormalizedProductFunctor a b).obj (A, B)) s ≅
      (T.binaryNormalizedProductFunctor a b).obj
        (T.segmentFactor A s, T.segmentFactor B s) := by
  let := T.topology
  let eTensor :
      (twist (T.determinantPowerCharacter (a + b) s)
        (BinaryTensor.rankZeroLeft (R := F.Carrier) ha A B.representation)).Equiv
      (BinaryTensor.rankZeroLeft (R := F.Carrier) ha
        (T.segmentFactor A s) (T.segmentFactor B s).representation) := by
    refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_
    intro g
    apply TensorProduct.ext'
    intro v w
    change (T.determinantPowerCharacter (a + b) s g : ℂ) •
        (v ⊗ₜ[ℂ] B.representation
          (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : a + b = b)) g) w) =
      v ⊗ₜ[ℂ] ((T.determinantPowerCharacter b s
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : a + b = b)) g) : ℂ) •
          B.representation
            (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : a + b = b)) g) w)
    rw [determinantPowerCharacter_reindex T]
    rw [TensorProduct.tmul_smul]
  exact SmoothRep.mkIso
    ((twistEquiv (T.determinantPowerCharacter (a + b) s)
      (T.binaryLeftZeroTensorEquiv ha (A, B))).trans
        (eTensor.trans
          (T.binaryLeftZeroTensorEquiv ha (T.segmentFactor A s, T.segmentFactor B s)).symm))

private def binaryRightZeroRealTwistIso (hb : b = 0) :
    letI := T.topology
    T.segmentFactor ((T.binaryNormalizedProductFunctor a b).obj (A, B)) s ≅
      (T.binaryNormalizedProductFunctor a b).obj
        (T.segmentFactor A s, T.segmentFactor B s) := by
  let := T.topology
  let eTensor :
      (twist (T.determinantPowerCharacter (a + b) s)
        (BinaryTensor.rankZeroRight (R := F.Carrier) hb A.representation B)).Equiv
      (BinaryTensor.rankZeroRight (R := F.Carrier) hb
        (T.segmentFactor A s).representation (T.segmentFactor B s)) := by
    refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_
    intro g
    apply TensorProduct.ext'
    intro v w
    change (T.determinantPowerCharacter (a + b) s g : ℂ) •
        (A.representation
          (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : a + b = a)) g) v ⊗ₜ[ℂ] w) =
      ((T.determinantPowerCharacter a s
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : a + b = a)) g) : ℂ) •
          A.representation
            (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : a + b = a)) g) v) ⊗ₜ[ℂ] w
    rw [determinantPowerCharacter_reindex T]
    rfl
  exact SmoothRep.mkIso
    ((twistEquiv (T.determinantPowerCharacter (a + b) s)
      (T.binaryRightZeroTensorEquiv hb (A, B))).trans
        (eTensor.trans
          (T.binaryRightZeroTensorEquiv hb (T.segmentFactor A s, T.segmentFactor B s)).symm))

private def binaryPositiveRealTwistIso (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    T.segmentFactor ((T.binaryNormalizedProductFunctor a b).obj (A, B)) s ≅
      (T.binaryNormalizedProductFunctor a b).obj
        (T.segmentFactor A s, T.segmentFactor B s) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨realPowerCharacter T.normalizedAbsUnits s,
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s⟩
  let C := Langlands.GeneralLinear.BlockShape.binary a b ha hb
  let σ := (T.binaryPairFamilyFunctor ha hb).obj (A, B)
  let e :
      (twist (T.determinantPowerCharacter (a + b) s)
        ((T.binaryPositiveProductFunctor ha hb).obj (A, B)).representation).Equiv
      ((T.binaryPositiveProductFunctor ha hb).obj
        (T.segmentFactor A s, T.segmentFactor B s)).representation := by
    refine (T.normalizedProductDeterminantTwistEquiv C χ
      (fun i => (σ i).representation)).trans
        (T.normalizedProductInducedEquiv C (fun i => ?_))
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => Fin.elim0 z) j) i
    · exact Representation.Equiv.refl _
    · exact Representation.Equiv.refl _
  exact SmoothRep.twistIso (T.determinantPowerCharacter (a + b) s)
      (T.isOpen_ker_determinantPowerCharacter (a + b) s)
      ((T.binaryNormalizedProductPositiveIso ha hb).app (A, B)) ≪≫
    SmoothRep.mkIso e ≪≫
    ((T.binaryNormalizedProductPositiveIso ha hb).app
      (T.segmentFactor A s, T.segmentFactor B s)).symm

/-- A common real determinant twist commutes with the literal normalized binary
product, including either or both ranks zero. -/
def binaryNormalizedProductRealTwistIso :
    letI := T.topology
    T.segmentFactor ((T.binaryNormalizedProductFunctor a b).obj (A, B)) s ≅
      (T.binaryNormalizedProductFunctor a b).obj
        (T.segmentFactor A s, T.segmentFactor B s) := by
  by_cases ha : a = 0
  · exact binaryLeftZeroRealTwistIso T A B s ha
  by_cases hb : b = 0
  · exact binaryRightZeroRealTwistIso T A B s hb
  exact binaryPositiveRealTwistIso T A B s (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)

end Langlands.PadicField.TopologicalData
