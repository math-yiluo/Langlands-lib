import Langlands.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration

/-!
# Splitting a segment product into its first factor and its tail

For a segment-product datum `d` with at least two segments, the actual product
`d.induced` is isomorphic to the rank cast of the binary product of its first
block with the product of the remaining blocks.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentProductSplit

open GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Normalized product induction on a rank-cast shape is the rank cast of the
product on the original shape. -/
theorem normalizedProductInductionFunctor_rankCast_obj {m n : ℕ} (C : BlockShape m)
    (h : m = n)
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (C.rankCast h)).obj X =
      (generalLinearRankCast T h).obj ((T.normalizedProductInductionFunctor C).obj X) := by
  subst h
  rfl

/-- The binary product of positive ranks, written as a product on the binary shape. -/
theorem binaryNormalizedProductFunctor_obj_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.binary a b ha hb).size i)
        F.Carrier))
    (h0 : X (0 : Fin 2) = A) (h1 : X (1 : Fin 2) = B) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a b).obj (A, B) =
      (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj X := by
  let _ := T.topology
  rw [T.binaryNormalizedProductFunctor_of_pos ha hb]
  change (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj
      ((T.binaryPairFamilyFunctor ha hb).obj (A, B)) = _
  congr 1
  funext i
  fin_cases i
  · exact h0.symm
  · exact h1.symm

variable {T}

/-- The datum of all segments after the first. -/
def tail {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (h : d.length = k + 2) :
    SegmentProductDatum.{uV, uF} T (d.shape.tailRank h) where
  length := k + 1
  segments j := d.segments (d.shape.tailIndex h j)
  degree_sum := rfl
  blocks j := d.blocks (d.shape.tailIndex h j)

theorem tail_segments {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (h : d.length = k + 2)
    (j : Fin (k + 1)) :
    (tail d h).segments j = d.segments (Fin.cast h.symm j.succ) := rfl

theorem tail_hasSegmentSocles {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = k + 2) (hd : d.HasSegmentSocles) : (tail d h).HasSegmentSocles :=
  fun _ => hd _

/-- The first factor and the product of the remaining factors. -/
theorem nonempty_iso_binary {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = k + 2) :
    letI := T.topology
    Nonempty (d.induced ≅ (generalLinearRankCast T (d.shape.headRank_add_tailRank h)).obj
      ((T.binaryNormalizedProductFunctor (d.shape.headRank h) (d.shape.tailRank h)).obj
        (d.blocks (d.shape.headIndex h), (tail d h).induced))) := by
  let _ := T.topology
  let e1 := T.headTailProductInductionIso d.shape h d.blocks
  let lift := SmoothRep.universeLift.{uF} (d.blocks (d.shape.headIndex h))
  have hX : (T.normalizedProductInductionFunctor (d.shape.headTailShape h)).obj
      (T.headTailProductFactors d.shape h d.blocks) =
      (generalLinearRankCast T (d.shape.headRank_add_tailRank h)).obj
        ((T.binaryNormalizedProductFunctor (d.shape.headRank h) (d.shape.tailRank h)).obj
          (lift, (tail d h).induced)) := by
    rw [binaryNormalizedProductFunctor_obj_eq T (d.shape.headRank_pos h)
      (d.shape.tailRank_pos h) lift (tail d h).induced
      (T.headTailProductFactors d.shape h d.blocks) rfl rfl]
    exact normalizedProductInductionFunctor_rankCast_obj T _ _ _
  let eL : lift ≅ d.blocks (d.shape.headIndex h) :=
    SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} (d.blocks (d.shape.headIndex h))).symm
  exact ⟨e1 ≪≫ eqToIso hX ≪≫ (generalLinearRankCast T _).mapIso
    ((T.binaryNormalizedProductFunctor _ _).mapIso (Iso.prod eL (Iso.refl _)))⟩

end Langlands.Classification.SegmentProductSplit
