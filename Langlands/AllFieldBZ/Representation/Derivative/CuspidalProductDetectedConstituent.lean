import Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.AllFieldBZ.Representation.Derivative.FiniteTopLine
import Langlands.AllFieldBZ.Representation.Derivative.TopLine
import Langlands.AllFieldBZ.Representation.Filtration.ExactFunctorDetectedConstituent
import Langlands.Representation.Derivative.CuspidalProductDetectedConstituent

/-!
# All-field port of `Langlands.Representation.Derivative.CuspidalProductDetectedConstituent`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.CuspidalProductDetectedConstituent` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open CategoryTheory.Limits
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding CuspidalProductDetectedConstituentData GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso chooseCuspidalProductDetectedConstituent cuspidalProductTopDerivativeLineEquiv finiteProductTopDerivativeLineEquiv generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero topDerivativeLineEquiv topProductIso topProductTensorEquiv
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private def _root_.Langlands.Derivative.positiveCuspidalTopLine {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (hirr : letI := T.topology; A.IsIrreducible)
    (hsc : letI := T.topology; IsSupercuspidal A.representation) :
    letI := T.topology
    ((generalLinearDerivative T ψ r r le_rfl).obj A) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  cases r with
  | zero => exact (Nat.not_lt_zero _ hr).elim
  | succ m =>
    exact topDerivativeLineEquiv T ψ m A hirr hsc.1
      (Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivative_top
        T ψ m A hsc
        (Classification.SupercuspidalTopDerivative.nontrivial_of_isIrreducible
          A.representation hirr))

set_option maxHeartbeats 800000 in
/-- The whole top derivative of a positive-rank ordered product of actual
supercuspidal factors is linearly equivalent to the complex scalars. -/
def cuspidalProductTopDerivativeLineEquiv {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (C : letI := T.topology;
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj))) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  let σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (B.size i) F.Carrier) :=
    fun i => SmoothRep.universeLift.{uF} (C i).obj
  have hirr (i) : (σ i).IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff (C i).obj).mpr (C i).property.1
  have hsc (i) : IsSupercuspidal (σ i).representation :=
    isSupercuspidal_of_equiv
      (SmoothRep.universeLiftEquiv.{uF} (C i).obj) (C i).property.2
  let e : ∀ i, ((generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj
      (σ i)) ≃ₗ[ℂ] ℂ :=
    fun i => positiveCuspidalTopLine T ψ (B.positive i) (σ i) (hirr i) (hsc i)
  let P := (T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)
  let Q := (T.normalizedProductInductionFunctor B).obj σ
  let E : P ≅ Q := SmoothRep.mkIso
    (T.normalizedProductInducedEquiv B
      (fun i => SmoothRep.universeLiftEquiv.{uF} (C i).obj))
  let J := generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl
  exact (SmoothRep.equivOfIso (J.mapIso E)).toLinearEquiv.trans
    (finiteProductTopDerivativeLineEquiv T ψ hn B σ e)

/-- Actual selected constituent and top-line data for one fixed ordered product.
The equivalences in `detected` concern the same ambient product. -/
structure CuspidalProductDetectedConstituentData {n : ℕ}
    (B : BlockShape n)
    (C : letI := T.topology;
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) where
  topLine : letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj))) ≃ₗ[ℂ] ℂ
  finite_length : letI := T.topology
    ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)).HasFiniteLength
  detected : letI := T.topology
    ExactFunctorDetectedConstituent.Data (generalLinearDerivative T ψ n n le_rfl)
      ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj))

/-- Choose the unique nondegenerate irreducible constituent class of a fixed
positive-rank ordered supercuspidal product, as actual constituent data. -/
def chooseCuspidalProductDetectedConstituent {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (C : letI := T.topology;
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    CuspidalProductDetectedConstituentData T ψ B C := by
  letI := T.topology
  let P := (T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)
  let J := generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl
  let e := cuspidalProductTopDerivativeLineEquiv T ψ hn B C
  have hP : P.HasFiniteLength :=
    Classification.irreducibleProductFiniteLength F T n hn B
      (fun i => (C i).obj) (fun i => (C i).property.1)
  have hJ : Mirabolic.MapsShortExactIntertwiners J :=
    generalLinearDerivativeExactness F T ψ n n le_rfl
  letI := ExactFunctorIrreducibility.preservesZero_of_exact J hJ
  have hirr : (J.obj P).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one (J.obj P)
      (e.finrank_eq.trans (Module.finrank_self ℂ))
  exact
    { topLine := e
      finite_length := hP
      detected := ExactFunctorDetectedConstituent.choose J hJ P hP hirr }

end Langlands.AllFieldBZ.Derivative
