import Langlands.AllFieldBZ.Representation.Derivative.LeibnizPieceCompat
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductRestrictionStatement
import Langlands.Representation.Derivative.LeibnizRestrictionCompat

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizRestrictionCompat`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizRestrictionCompat` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionSubobjectSourceIso leibnizSource level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource
universe uF uV

variable {F : LocalFieldPackage.{uF}}

open Langlands.Derivative.MirabolicProductRestriction hiding restrictedProduct restrictionQuotient restrictionSubobject
open Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction
/-- Differentiating the restricted product gives the literal Leibniz source,
after the equality-based output rank transport. -/
def leibnizRestrictedProductSourceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    letI := T.topology
    Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct.{uF, uV} T m n ⋙
      mirabolicDerivativeOfOrder T ψ (m + n + 1) d (by omega) ⋙
      SmoothRep.toRep ⋙
      generalLinearRepRankCast.{uF, max uF uV} (F := F)
        (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) ≅
    leibnizSource T ψ (m + 1) (n + 1) d hd.2 := by
  letI := T.topology
  let h : (m + 1) + (n + 1) = (m + n + 1) + 1 := by omega
  let hD : 0 < d ∧ d ≤ (m + n + 1) + 1 := by omega
  refine Functor.isoWhiskerLeft
    (T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙ generalLinearRankCast T h)
    (Functor.isoWhiskerRight
      (generalLinearRestrictionDerivativeIso T ψ (m + n + 1) d hD)
      (SmoothRep.toRep ⋙ generalLinearRepRankCast (F := F) (by omega))) ≪≫ ?_
  refine Functor.isoWhiskerLeft (T.binaryNormalizedProductFunctor (m + 1) (n + 1))
    (Functor.isoWhiskerRight
      (generalLinearRankCastDerivativeIso T ψ h d hd.2 hD.2)
      (SmoothRep.toRep ⋙ generalLinearRepRankCast (F := F) (by omega))) ≪≫ ?_
  apply eqToIso
  simp only [leibnizSource, Functor.assoc, ← generalLinearRankCast_toRep]
  rw [← Functor.assoc (generalLinearRankCast T (congrArg (fun r => r - d) h))
    (generalLinearRankCast T (show (m + n + 1) + 1 - d =
      ((m + 1) + (n + 1)) - d by omega)) SmoothRep.toRep,
    generalLinearRankCast_trans]
  rfl

/-- Differentiating the restriction subobject is the actual right-mixed
derivative source, precomposed by restriction on the first input, with the
same final output rank. -/
def leibnizRestrictionSubobjectSourceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    letI := T.topology
    Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionSubobject.{uF, uV} T m n ⋙
      mirabolicDerivativeOfOrder T ψ (m + n + 1) d (by omega) ⋙
      SmoothRep.toRep ⋙
      generalLinearRepRankCast.{uF, max uF uV} (F := F)
        (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) ≅
    (generalLinearRestriction T m).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
      rightMixedDerivativeSource T ψ (n + 1) m d (by omega) ⋙
      generalLinearRepRankCast.{uF, max uF uV} (F := F)
        (show ((n + 1) + m) + 1 - d = ((m + 1) + (n + 1)) - d by omega) := by
  letI := T.topology
  refine Functor.isoWhiskerLeft
    ((generalLinearRestriction T m).prod (𝟭 _) ⋙ T.rightMixedProductFunctor (n + 1) m)
    (Functor.isoWhiskerRight
      (mirabolicRankCastDerivativeIso T ψ
        (show (n + 1) + m = m + n + 1 by omega) d (by omega) (by omega))
      (SmoothRep.toRep ⋙ generalLinearRepRankCast (F := F) (by omega))) ≪≫ ?_
  apply eqToIso
  simp only [rightMixedDerivativeSource, Functor.assoc, ← generalLinearRankCast_toRep]
  rw [← Functor.assoc
    (generalLinearRankCast T (congrArg (fun r => r + 1 - d)
      (show (n + 1) + m = m + n + 1 by omega)))
    (generalLinearRankCast T (show (m + n + 1) + 1 - d =
      ((m + 1) + (n + 1)) - d by omega)) SmoothRep.toRep,
    generalLinearRankCast_trans]

end Langlands.AllFieldBZ.Derivative
