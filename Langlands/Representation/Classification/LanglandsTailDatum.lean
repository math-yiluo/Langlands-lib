import Langlands.Representation.Classification.LanglandsData
import Langlands.Group.GL.HeadTailBlocks

/-! The original ordered tail of a genuine tempered Langlands datum. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.TemperedLanglandsDatum

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n k : ℕ}
  (d : TemperedLanglandsDatum.{uV, uF} T n) (h : d.shape.length = k + 2)

/-- Remove the first block, retaining the original blocks and real exponents
in their original order. -/
def tail : TemperedLanglandsDatum.{uV, uF} T (d.shape.tailRank h) where
  shape := d.shape.tailShape h
  blocks j := d.blocks (d.shape.tailIndex h j)
  irreducible j := d.irreducible (d.shape.tailIndex h j)
  tempered j := d.tempered (d.shape.tailIndex h j)
  exponent j := d.exponent (d.shape.tailIndex h j)
  strictAnti := d.strictAnti.comp_strictMono (d.shape.tailIndex_strictMono h)

@[simp]
theorem tail_shape : (d.tail h).shape = d.shape.tailShape h := rfl

@[simp]
theorem tail_blocks (j : Fin (k + 1)) :
    (d.tail h).blocks j = d.blocks (d.shape.tailIndex h j) := rfl

@[simp]
theorem tail_exponent (j : Fin (k + 1)) :
    (d.tail h).exponent j = d.exponent (d.shape.tailIndex h j) := rfl

/-- The restricted datum has fewer blocks, so it is an induction input. -/
theorem tail_length_lt : (d.tail h).shape.length < d.shape.length := by
  change k + 1 < d.shape.length
  omega

/-- Every exponent in the ordered tail is smaller than the first exponent. -/
theorem tail_exponent_lt_head (j : Fin (k + 1)) :
    (d.tail h).exponent j < d.exponent (d.shape.headIndex h) :=
  d.strictAnti (d.shape.headIndex_lt_tailIndex h j)

/-- Twisting the restricted datum uses exactly the original twisted blocks. -/
theorem tail_twistedBlocks :
    T.twistedBlocks (d.tail h).shape (d.tail h).blocks (d.tail h).exponent =
      (fun j => T.twistedBlocks d.shape d.blocks d.exponent
        (d.shape.tailIndex h j)) := rfl

/-- The tail standard module is the actual normalized product of the remaining
original twisted factors, with no additional carrier lift. -/
theorem tail_standardModule :
    (d.tail h).standardModule =
      (T.normalizedProductInductionFunctor (d.shape.tailShape h)).obj
        (fun j => T.twistedBlocks d.shape d.blocks d.exponent
          (d.shape.tailIndex h j)) := rfl

end Langlands.PadicField.TopologicalData.TemperedLanglandsDatum
