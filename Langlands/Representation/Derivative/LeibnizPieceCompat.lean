import Langlands.Representation.Derivative.RankCastCompat
import Langlands.Representation.Derivative.LeibnizIndices

/-! Natural identification of the positive-first mixed grades with Leibniz grades. -/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Equality-based rank transport for the underlying representations. -/
def generalLinearRepRankCast {a b : ℕ} (h : a = b) :
    Rep.{uV} ℂ (GeneralLinear a F.Carrier) ⥤
      Rep.{uV} ℂ (GeneralLinear b F.Carrier) :=
  h ▸ 𝟭 _

/-- Forgetting smoothness commutes with the same equality-based rank transport. -/
theorem generalLinearRankCast_toRep (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h ⋙ SmoothRep.toRep =
      SmoothRep.toRep ⋙ generalLinearRepRankCast.{uF, uV} (F := F) h := by
  let _ := T.topology
  subst b
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

/-- The unchanged right-mixed grade, restricted on its first input and with the
total-rank cast applied in `SmoothRep` before forgetting, is its Leibniz grade. -/
def leibnizPositiveSmoothPieceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m b d : ℕ) (x : RightMixedDerivativeIndex b m d) :
    letI := T.topology
    (generalLinearRestriction.{uF, uV} T m).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))) ⋙
      (mirabolicDerivativeOfOrder T ψ m x.val.1
          (rightMixedDerivativeIndices_left_bound x.property)).prod
        (generalLinearDerivative T ψ b x.val.2
          (rightMixedDerivativeIndices_right_le x.property)) ⋙
      T.binaryNormalizedProductFunctor (m + 1 - x.val.1) (b - x.val.2) ⋙
      generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property) ⋙
      generalLinearRankCast T
        (show (b + m) + 1 - d = ((m + 1) + b) - d by omega) ⋙
      SmoothRep.toRep ≅
    leibnizPiece T ψ (m + 1) b d (leibnizPositiveIndex x) := by
  letI := T.topology
  let D := generalLinearDerivative.{uF, uV} T ψ b x.val.2
    (rightMixedDerivativeIndices_right_le x.property)
  let e := NatIso.prod
    (generalLinearRestrictionDerivativeIso.{uF, uV} T ψ m x.val.1
      (rightMixedDerivativeIndices_left_bound x.property))
    (eqToIso (Functor.id_comp D))
  refine (Functor.isoWhiskerRight e
    (T.binaryNormalizedProductFunctor (m + 1 - x.val.1) (b - x.val.2) ⋙
      generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property) ⋙
      generalLinearRankCast T
        (show (b + m) + 1 - d = ((m + 1) + b) - d by omega) ⋙
      SmoothRep.toRep)) ≪≫ ?_
  apply eqToIso
  simp only [leibnizPiece, leibnizPositiveIndex, D, ← Functor.assoc,
    generalLinearRankCast_trans]
  rfl

/-- Direct comparison with the published `Rep`-valued right-mixed grade.
The forgetting square expresses the output transport as the actual smooth
rank cast before `SmoothRep.toRep`. -/
def leibnizPositivePieceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m b d : ℕ) (x : RightMixedDerivativeIndex b m d) :
    letI := T.topology
    (generalLinearRestriction.{uF, uV} T m).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))) ⋙
      rightMixedDerivativePiece T ψ b m d x ⋙
      generalLinearRepRankCast.{uF, max uF uV} (F := F)
        (show (b + m) + 1 - d = ((m + 1) + b) - d by omega) ≅
    leibnizPiece T ψ (m + 1) b d (leibnizPositiveIndex x) := by
  letI := T.topology
  refine (eqToIso ?_) ≪≫ leibnizPositiveSmoothPieceIso T ψ m b d x
  simp only [rightMixedDerivativePiece, Functor.assoc, ← generalLinearRankCast_toRep]

end Langlands.Derivative
