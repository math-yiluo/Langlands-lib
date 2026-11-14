import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.AllFieldBZ.Representation.Derivative.RankCastCompat
import Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
import Langlands.Representation.Derivative.LeibnizPieceCompat

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizPieceCompat`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizPieceCompat` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous RightMixedProductDerivativeFiltrationStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizSource level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource
universe uF uV

variable {F : LocalFieldPackage.{uF}}

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

end Langlands.AllFieldBZ.Derivative
