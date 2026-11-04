import Langlands.Representation.Derivative.InducedMapQuotient
import Langlands.Representation.Derivative.PartialDerivativeTensorProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Shahidi.IntertwiningInduced

/-! # Actual derivative quotients for binary tensor induction -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {k m : ℕ} (hk : 0 < k) (hm : 0 < m)

/-- The indexed exterior tensor of two smooth factors on the actual positive
binary Levi. The first block acts on the first factor. -/
def binaryLeviTensor :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) →
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier) →
      SmoothRep.{0,uF,uV} ℂ ((Shahidi.twoBlocks k m hk hm).Levi F.Carrier) := by
  letI := T.topology
  intro A B
  exact FiniteTensor.externalSmoothObject (Fin.cases A (Fin.cases B finZeroElim))

/-- Pulling the indexed Levi tensor back to the product of its two factors
identifies it with the raw binary exterior tensor. -/
def binaryLeviTensorPullbackIso :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier)),
      (positiveTwoBlockLeviPullback T k m hk hm).obj
          (binaryLeviTensor T hk hm A B) ≅
        (exteriorTensor T k m).obj (A, B) := by
  letI := T.topology
  intro A B
  let fam : ∀ i : Fin 2, SmoothRep.{0,uF,uV} ℂ
      (GeneralLinear ((Shahidi.twoBlocks k m hk hm).size i) F.Carrier) :=
    Fin.cases A (Fin.cases B finZeroElim)
  refine SmoothRep.mkIso
    { toLinearEquiv := Shahidi.pairSplit (fun i => (fam i : Type uV))
      isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  change Shahidi.pairSplit (fun i => (fam i : Type uV))
      (FiniteTensor.external (fun i => (fam i).representation)
        ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm g) x) = _
  exact Shahidi.pairSplit_external (fun i => (fam i).representation)
    ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm g) x

/-- Irreducible admissible factors have an irreducible indexed Levi tensor. -/
theorem binaryLeviTensor_isIrreducible :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier)),
      Representation.IsIrreducible A.representation →
      Representation.IsIrreducible B.representation →
      A.IsAdmissible → B.IsAdmissible →
      Representation.IsIrreducible (binaryLeviTensor T hk hm A B).representation := by
  let := T.topology
  intro A B hA hB ha hb
  let fam : ∀ i : Fin 2, SmoothRep.{0,uF,uV} ℂ
      (GeneralLinear ((Shahidi.twoBlocks k m hk hm).size i) F.Carrier) :=
    Fin.cases A (Fin.cases B finZeroElim)
  have hi : ∀ i, Representation.IsIrreducible (fam i).representation := by
    intro i
    fin_cases i <;> assumption
  have hadm : ∀ i, (fam i).IsAdmissible := by
    intro i
    fin_cases i <;> assumption
  let := hi
  exact FiniteTensor.isIrreducible_external (fun i => (fam i).representation)
    (fun i f => (admissibleSchur_scalarEndomorphism _ (hadm i) (hi i) f).exists)

/-- A nonzero actual map into induction of an irreducible admissible binary
tensor supplies a surjective map onto the first factor tensored with the top
derivative of the second. No derivative nonvanishing premise is imposed. -/
def binaryTensorDerivativeQuotientOfInducedMap
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier))
      (_hA : Representation.IsIrreducible A.representation)
      (_hB : Representation.IsIrreducible B.representation)
      (_ha : A.IsAdmissible) (_hb : B.IsAdmissible)
      (j : X.representation.IntertwiningMap
        (T.normalizedParabolicInduced (Shahidi.twoBlocks k m hk hm)
          (binaryLeviTensor T hk hm A B).representation)),
      j ≠ 0 →
        {q : ((generalLinearDerivative T ψ (k + m) m (Nat.le_add_left m k) ⋙
                generalLinearRankCast T (Nat.add_sub_cancel k m)).obj X) ⟶
            (firstFactorTopDerivative T ψ k m).obj (A, B) //
          Function.Surjective (SmoothRep.hom q)} := by
  letI := T.topology
  intro X A B hA hB ha hb j hj
  let σ := binaryLeviTensor T hk hm A B
  let q := derivativeQuotientOfInducedMap T ψ k m hk hm X σ
    (binaryLeviTensor_isIrreducible T hk hm A B hA hB ha hb) j hj
  let e := (partialDerivative T ψ k m).mapIso
    (binaryLeviTensorPullbackIso T hk hm A B)
  let t := (Classical.choice (partialDerivativeTensor F T ψ k m)).app (A, B)
  refine ⟨q.val ≫ e.hom ≫ t.hom, ?_⟩
  exact (SmoothRep.equivOfIso t).surjective.comp
    ((SmoothRep.equivOfIso e).surjective.comp q.property)

end Langlands.Derivative
