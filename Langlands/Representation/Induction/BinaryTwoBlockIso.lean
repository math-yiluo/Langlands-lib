import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Shahidi.TwoBlocks

/-! # Positive binary products on the explicit two-block shape -/

noncomputable section

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData)

private theorem binaryShape_eq_twoBlocks {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    GeneralLinear.BlockShape.binary a b ha hb = Shahidi.twoBlocks a b ha hb := by
  unfold GeneralLinear.BlockShape.binary Shahidi.twoBlocks
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem productObject_congr {n : ℕ}
    {L M : GeneralLinear.BlockShape n} (h : L = M)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (L.size i) F.Carrier))
    (B : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (M.size i) F.Carrier))
    (hAB : HEq A B) :
    letI := T.topology
    (T.normalizedProductInductionFunctor L).obj A =
      (T.normalizedProductInductionFunctor M).obj B := by
  subst h
  cases hAB
  rfl

/-- A positive binary normalized product is the actual normalized induction
of the ordered family `(A,B)` on the explicit Shahidi two-block shape. -/
def binaryNormalizedProductTwoBlockIso {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      (T.binaryNormalizedProductFunctor a b).obj (A,B) ≅
        (T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
          (Fin.cases A (Fin.cases B finZeroElim)) := by
  letI := T.topology
  intro A B
  apply eqToIso
  rw [T.binaryNormalizedProductFunctor_of_pos ha hb]
  change (T.normalizedProductInductionFunctor
      (GeneralLinear.BlockShape.binary a b ha hb)).obj
      ((T.binaryPairFamilyFunctor ha hb).obj (A,B)) = _
  apply productObject_congr T (binaryShape_eq_twoBlocks ha hb)
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  fin_cases i <;> rfl

end Langlands.PadicField.TopologicalData
