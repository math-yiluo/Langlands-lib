import Langlands.AllFieldBZ.Representation.Derivative.LeibnizPieceCompat
import Langlands.Representation.Derivative.LeibnizZeroFirstPiece

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizZeroFirstPiece`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizZeroFirstPiece` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous RightMixedProductDerivativeFiltrationStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizSource leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- Restricting the second factor to the mirabolic subgroup and taking its positive
order-`d` mirabolic derivative, then the binary product with the unchanged first
factor, the total rank cast in `SmoothRep` and forgetting smoothness, is naturally
the Leibniz grade at the zero-first index `(0, d)`. -/
def leibnizZeroFirstSmoothPieceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ n + 1) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
        (generalLinearRestriction.{uF, uV} T n) ⋙
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
        (mirabolicDerivativeOfOrder T ψ n d hd) ⋙
      T.binaryNormalizedProductFunctor (m + 1) (n + 1 - d) ⋙
      generalLinearRankCast T (leibnizZeroFirst_rank (m := m) hd.2) ⋙
      SmoothRep.toRep ≅
    leibnizPiece T ψ (m + 1) (n + 1) d (leibnizZeroFirstIndex m (n + 1) d hd.2) := by
  letI := T.topology
  exact Functor.isoWhiskerRight
    (NatIso.prod (Iso.refl (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))))
      (generalLinearRestrictionDerivativeIso.{uF, uV} T ψ n d hd))
    (T.binaryNormalizedProductFunctor (m + 1) (n + 1 - d) ⋙
      generalLinearRankCast T (leibnizZeroFirst_rank (m := m) hd.2) ⋙
      SmoothRep.toRep)

end Langlands.AllFieldBZ.Derivative
