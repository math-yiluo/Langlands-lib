import Langlands.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration

/-! The published head/tail regrouping with the literal all-rank binary product. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.PadicField.TopologicalData

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Equality transport of the ambient rank agrees with transporting the shape. -/
def normalizedProductInductionRankTransportIso {m n : ℕ} (h : m = n)
    (B : BlockShape m)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (Derivative.generalLinearRankCast T h).obj
        ((T.normalizedProductInductionFunctor B).obj σ) ≅
      (T.normalizedProductInductionFunctor (B.rankCast h)).obj σ := by
  cases h
  exact Iso.refl _

variable {n k : ℕ} (B : BlockShape n) (h : B.length = k + 2)

/-- Split a product into its original first factor and actual ordered tail,
using the literal binary functor and the prescribed ambient rank equality. -/
def headTailBinaryProductIso
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj σ ≅
      (Derivative.generalLinearRankCast T (B.headRank_add_tailRank h)).obj
        ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj
          (σ (B.headIndex h),
            (T.normalizedProductInductionFunctor (B.tailShape h)).obj
              (fun j => σ (B.tailIndex h j)))) := by
  letI := T.topology
  let A := σ (B.headIndex h)
  let C := (T.normalizedProductInductionFunctor (B.tailShape h)).obj
    (fun j => σ (B.tailIndex h j))
  let factors := (T.binaryPairFamilyFunctor (B.headRank_pos h) (B.tailRank_pos h)).obj (A, C)
  let e : T.headTailProductFactors B h σ ≅ factors :=
    CategoryTheory.Pi.isoMk (fun i => match i with
      | 0 => SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} A).symm
      | 1 => Iso.refl _)
  let regrouped := T.headTailProductInductionIso B h σ ≪≫
    (T.normalizedProductInductionFunctor (B.headTailShape h)).mapIso e
  let rankIso := T.normalizedProductInductionRankTransportIso
    (B.headRank_add_tailRank h)
    (BlockShape.binary (B.headRank h) (B.tailRank h)
      (B.headRank_pos h) (B.tailRank_pos h)) factors
  let binaryIso := (Derivative.generalLinearRankCast T (B.headRank_add_tailRank h)).mapIso
    ((T.binaryNormalizedProductPositiveIso (B.headRank_pos h) (B.tailRank_pos h)).app (A, C))
  exact regrouped ≪≫ rankIso.symm ≪≫ binaryIso.symm

end Langlands.PadicField.TopologicalData
