import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductHomogeneityProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusCompatibility
import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductHeadShift
import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement
import Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductPhiMinusDetectionProof
import Langlands.AllFieldBZ.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof

/-!
# All-field port of `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing LeftMixedProductHomogeneity MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement OrderedCuspidalProductNoDegenerateSubmodules PartialDerivativeJacquetComparisonStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff hasNonzeroDerivative_of_isHomogeneous isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProductHomogeneity leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeAdjunction mirabolicDerivativeAdjunction_comp_left mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrderAdjunction mirabolicDerivativeOfOrderAdjunction_comp_left mirabolicDerivativeOfOrderAdjunction_unit mirabolicDerivativeOfOrderAdjunction_unit_comp mirabolicDerivativeOfOrderRightAdjoint mirabolicDerivativeOfOrderUnit mirabolicDerivativeOfOrderUnitKer mirabolicDerivativeOfOrderUnit_injective mirabolicDerivativeOfOrderUnit_injective_of_forall mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp mirabolicDerivativeOfOrder_map_injective mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivativeRightAdjoint mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicProductMinusCompatibility mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCastHomEquiv mirabolicRankCastHomEquiv_comp_left mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans orderedCuspidalProductNoDegenerateSubmodules partialDerivative partialDerivativeJacquetComparison partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiHatPlusIterate phiHatPlusIterateAdjunction phiHatPlusIterateAdjunction_comp_left phiHatPlusIterateAdjunction_succ phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast positiveTwoBlockNormalizedJacquet rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero rightMixedProductPhiMinusDetection subsingleton_mirabolicDerivativeOfOrder_unit_ker
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV uW

namespace OrderedCuspidalProductNondegeneracy
open Langlands.Derivative.OrderedCuspidalProductNondegeneracy hiding Good HeadExclusion Ordered binaryLineIso binaryShapeIso caseTwo_false exists_injective_of_rankCast finrank_binaryProduct_rank_zero finrank_generalLinearDerivative_order finrank_generalLinearRankCast finrank_generalLinearRankCast_top finrank_graded_of_length_one finrank_topLeibnizPiece finrank_top_binaryProduct generalLinearRankCast_comp_obj generalLinearRankCast_map_injective generalLinearRankCast_symm_obj good_of_iso good_of_supercuspidal good_product good_single good_step good_universeLift_of_supercuspidal hasNonzeroDerivative_eq_of_supercuspidal headExclusion_of_ordered headTailBridge level_of_good mirabolicDerivativeOfOrder_rankCast_obj nontrivial_subrepresentation_of_good nontrivial_top_of_good ordered_tail singleFamily_eq singletonProductLiftIso supercuspidalProperty_transport
variable {F : LocalFieldPackage.{uF}}

open Langlands.Derivative.LevelCalculus hiding hasNonzeroDerivative_iff_of_iso hasNonzeroDerivative_level hasNonzeroDerivative_of_injective hasNonzeroDerivative_succ_iff hasNonzeroDerivative_succ_iff_cast isHomogeneous_of_forall_injective isHomogeneous_of_iso level_eq_level_phiMinus_succ level_eq_of_isHomogeneous level_eq_of_iso level_le_level_phiMinus_succ level_le_max_of_isShortExact level_le_of_imp level_le_of_injective level_le_one_of_subsingleton_phiMinus level_mirabolicRankCast level_pos mapsShortExact_mirabolicDerivative mapsShortExact_mirabolicDerivativeOfOrder mapsShortExact_mirabolicRankCast mapsShortExact_phiMinusIterate mirabolicDerivative_succ_cast_obj nontrivial_mirabolicDerivative_cast_congr nontrivial_of_hasNonzeroDerivative nontrivial_phiMinus_iff
open Langlands.AllFieldBZ.Derivative.LevelCalculus
open Langlands.Derivative.RightMixedLevel hiding isHomogeneous_mirabolicRankCast level_eq_of_phiMinus_injective level_eq_succ_of_phiMinus level_of_injective_rightMixed level_of_injective_rightMixed_zero mirabolicDerivative_zero_cast_obj nontrivial_phiMinus_of_injective phiMinus_cast_map_injective
open Langlands.AllFieldBZ.Derivative.RightMixedLevel
open Langlands.Derivative.MirabolicProductRestriction hiding core determinantNorm_mirabolic exists_exact_comp_mirabolicRankCast exists_exact_restrictedCompactInduction factors generalLinearRankCast_comp_restriction inducingFunctor leviHalfModulus_eq_leftLeviCharacter leviHalfModulus_eq_rightLeviCharacter leviInducingFunctor leviModulus_shape midEquiv midEquiv_naturality midFunctor mirabolicRankCast_comp mirabolicRankCast_eq_pullback pair_hT quotEquiv quotEquiv_naturality quotFunctor quot_hE restrictedProduct restrictedProduct_eq restrictionQuotient restrictionQuotient_eq restrictionSubobject restrictionSubobject_eq subEquiv subEquiv_naturality subFunctor sub_hE tensorEquiv topologicalRing
open Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction
open Langlands.Derivative.RestrictedProductLevel hiding hasNonzeroDerivative_leftMixed hasNonzeroDerivative_of_leftMixed isHomogeneous_restrictedProduct le_level_leftMixed level_le_of_imp_of_rank level_leftMixed_le
open Langlands.AllFieldBZ.Derivative.RestrictedProductLevel
/-! ## Rank transports -/

section Casts
variable (T : F.TopologicalData)

theorem generalLinearRankCast_comp_obj {a b c : ℕ} (h : a = b) (h' : b = c) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      (generalLinearRankCast T h').obj ((generalLinearRankCast T h).obj X) =
        (generalLinearRankCast T (h.trans h')).obj X := by
  subst h h'
  intro X
  rfl

theorem generalLinearRankCast_symm_obj {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      (generalLinearRankCast T h.symm).obj ((generalLinearRankCast T h).obj X) = X := by
  subst h
  intro X
  rfl

theorem generalLinearRankCast_map_injective {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier)} (f : X ⟶ Y),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective (SmoothRep.hom ((generalLinearRankCast T h).map f)) := by
  subst h
  intro X Y f hf
  exact hf

theorem mirabolicDerivativeOfOrder_rankCast_obj
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b)
    (k : ℕ) (hk : 0 < k ∧ k ≤ b + 1) (hk' : 0 < k ∧ k ≤ a + 1) (h' : a + 1 - k = b + 1 - k) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (mirabolic a F.Carrier),
      (mirabolicDerivativeOfOrder T ψ b k hk).obj ((mirabolicRankCast T h).obj X) =
        (generalLinearRankCast T h').obj ((mirabolicDerivativeOfOrder T ψ a k hk').obj X) := by
  subst h
  intro X
  rfl

theorem finrank_generalLinearRankCast_top
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      Module.finrank ℂ ((generalLinearDerivative T ψ b b le_rfl).obj
          ((generalLinearRankCast T h).obj X)) =
        Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj X) := by
  subst h
  intro X
  rfl

/-- An injection into a rank cast of `Y`, where a rank cast of `Y` is isomorphic
to a rank cast of `D`, gives an injection into a rank cast of `D`. -/
theorem exists_injective_of_rankCast {a b a' c : ℕ} (h : a = b) (hA : a = a') (h2 : c = a')
    (h3 : c = b) :
    letI := T.topology
    ∀ {X Z : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)}
      {Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier)}
      {D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear c F.Carrier)} (f : X ⟶ Z),
      Function.Injective (SmoothRep.hom f) → Z = (generalLinearRankCast T h).obj Y →
      ((generalLinearRankCast T hA).obj Y ≅ (generalLinearRankCast T h2).obj D) →
        ∃ g : X ⟶ (generalLinearRankCast T h3).obj D, Function.Injective (SmoothRep.hom g) := by
  subst h hA h2
  let _ := T.topology
  intro X Z Y D f hf hZ e
  subst hZ
  exact ⟨f ≫ e.hom, (iso_hom_injective e).comp hf⟩

end Casts
/-! ## The induction invariant -/

section Good
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The restriction to the mirabolic subgroup is homogeneous and the top
derivative is one-dimensional. -/
def Good {n : ℕ} :
    letI := T.topology
    SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier) → Prop := by
  letI := T.topology
  exact fun X => IsHomogeneous T ψ ((generalLinearRestriction T n).obj X) ∧
    Module.finrank ℂ ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj X) = 1

theorem good_of_iso {n : ℕ} :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier)},
      (X ≅ Y) → Good T ψ X → Good T ψ Y := by
  let := T.topology
  intro X Y e hX
  refine ⟨Langlands.AllFieldBZ.Derivative.LevelCalculus.isHomogeneous_of_iso T ψ ((generalLinearRestriction T n).mapIso e) hX.1, ?_⟩
  exact (LinearEquiv.finrank_eq (SmoothRep.equivOfIso
    ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).mapIso e)).toLinearEquiv).symm.trans
      hX.2

/-- The top derivative of the restriction is nonzero. -/
theorem nontrivial_top_of_good {n : ℕ} :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier), Good T ψ X →
      Nontrivial ((mirabolicDerivativeOfOrder T ψ n (n + 1) ⟨Nat.zero_lt_succ n, le_rfl⟩).obj
        ((generalLinearRestriction T n).obj X)) := by
  let := T.topology
  intro X hX
  rw [← RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ le_rfl _ X]
  exact Module.nontrivial_of_finrank_eq_succ hX.2

theorem level_of_good {n : ℕ} :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier), Good T ψ X →
      level T ψ ((generalLinearRestriction T n).obj X) = n + 1 := by
  let := T.topology
  intro X hX
  exact le_antisymm (level_le T ψ _)
    (le_level_of_hasNonzeroDerivative T ψ _ ⟨_, nontrivial_top_of_good T ψ X hX⟩)

/-- Every nonzero subrepresentation of a good restriction has nonzero top derivative. -/
theorem nontrivial_subrepresentation_of_good {n : ℕ} :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier), Good T ψ X →
      ∀ U : Subrepresentation ((generalLinearRestriction T n).obj X).representation, U ≠ ⊥ →
        Nontrivial ((mirabolicDerivativeOfOrder T ψ n (n + 1)
          ⟨Nat.zero_lt_succ n, le_rfl⟩).obj
            (SmoothRep.subrepresentation ((generalLinearRestriction T n).obj X) U)) := by
  let := T.topology
  intro X hX U hU
  have hlev := hX.1 U hU
  rw [level_of_good T ψ X hX] at hlev
  obtain ⟨-, ⟨_, h⟩, -⟩ := (level_eq_iff T ψ (Nat.zero_lt_succ n) _).mp hlev
  exact h

end Good
/-! ## Irreducible supercuspidal representations -/

section Supercuspidal
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- By BZ77 4.4, the restriction of an irreducible supercuspidal representation
of `GL_(m+1)` has nonzero derivatives only in the top order. -/
theorem hasNonzeroDerivative_eq_of_supercuspidal {m : ℕ} :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (m + 1) F.Carrier),
      D.IsIrreducible → IsSupercuspidal D.representation →
        ∀ j, HasNonzeroDerivative T ψ ((generalLinearRestriction T m).obj D) j → j = m + 1 := by
  let := T.topology
  rintro D hirr hsc j ⟨hj, h⟩
  obtain ⟨hvan, -⟩ := Classification.supercuspidalDerivatives.{uF, uW} F T ψ m D hirr hsc
  by_contra hne
  obtain _ | i := j
  · exact absurd hj.1 (Nat.lt_irrefl 0)
  have hs := hvan (i + 1) hj.2 (Nat.succ_pos i) (lt_of_le_of_ne hj.2 hne)
  rw [RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ hj.2 hj D] at hs
  exact not_subsingleton _ hs

theorem good_of_supercuspidal {n : ℕ} :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier),
      D.IsIrreducible → IsSupercuspidal D.representation → Good T ψ D := by
  let := T.topology
  intro D hirr hsc
  exact ⟨RestrictionBridge.isHomogeneous_of_single_order T ψ (Mirabolic.minusExactness F T)
      (n + 1) _ (hasNonzeroDerivative_eq_of_supercuspidal T ψ D hirr hsc),
    (Classification.supercuspidalDerivatives.{uF, uW} F T ψ n D hirr hsc).2⟩

/-- The carrier lift of an irreducible supercuspidal representation is good. -/
theorem good_universeLift_of_supercuspidal {n : ℕ} :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      supercuspidalProperty X → Good T ψ (SmoothRep.universeLift.{uF} X) := by
  let := T.topology
  intro X hX
  exact good_of_supercuspidal T ψ _ ((SmoothRep.isIrreducible_universeLift_iff X).mpr hX.1)
    (isSupercuspidal_of_equiv (SmoothRep.universeLiftEquiv.{uF} _) hX.2)

end Supercuspidal
/-! ## Binary products with a one-dimensional `GL_0` factor -/

section Line
variable (T : F.TopologicalData)

/-- `D × V ≅ D` for a one-dimensional representation `V` of `GL_0`. -/
def binaryLineIso {a c : ℕ} (hc : c = 0) (h : a = a + c) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (V : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)),
      Module.finrank ℂ V = 1 →
        ((T.binaryNormalizedProductFunctor a c).obj (D, V) ≅
          (generalLinearRankCast T h).obj D) := by
  subst hc
  letI := T.topology
  intro D V hV
  haveI := Module.finite_of_finrank_eq_succ hV
  let eV : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V ℂ (by rw [hV, Module.finrank_self])
  exact (ZeroRankTensor.binaryRightZeroIso T a).app (D, V) ≪≫
    SmoothRep.mkIso (firstFactorLineEquiv D.representation _
      (ULift.moduleEquiv.trans eV))

end Line
/-! ## The top derivative of a binary product -/

section TopFinrank
/-- The only graded piece of a length-one filtration has the dimension of the source. -/
theorem finrank_graded_of_length_one {C : Type*} [Category C] {G : Type*} [Monoid G]
    {Φ : C ⥤ Rep.{uW} ℂ G} {n : ℕ} (s : RepFunctorFiltration Φ n) (hn : n = 1) (i : Fin n)
    (X : C) : Module.finrank ℂ ((s.graded i).obj X) = Module.finrank ℂ (Φ.obj X) := by
  subst hn
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : ((s.step (0 : Fin 1).castSucc).obj X).toSubmodule = ⊥ := by
    rw [show (s.step (0 : Fin 1).castSucc).obj X = ⊥ from s.zero X]
    rfl
  have h1 : ((s.step (0 : Fin 1).succ).obj X).toSubmodule = ⊤ := by
    rw [show (s.step (0 : Fin 1).succ).obj X = ⊤ from s.top X]
    rfl
  have hp : ((s.step (0 : Fin 1).castSucc).obj X).toSubmodule.comap
      ((s.step (0 : Fin 1).succ).obj X).toSubmodule.subtype = ⊥ := by
    rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
  calc Module.finrank ℂ ((s.graded 0).obj X)
      = Module.finrank ℂ ((s.step (0 : Fin 1).succ).obj X).toSubmodule :=
        LinearEquiv.finrank_eq (Submodule.quotEquivOfEqBot _ hp)
    _ = Module.finrank ℂ (Φ.obj X) := by rw [h1, finrank_top]

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem finrank_generalLinearRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      Module.finrank ℂ ((generalLinearRankCast T h).obj X) = Module.finrank ℂ X := by
  subst h
  intro X
  rfl

/-- A binary product whose second factor has rank zero has the dimension of the tensor
product of its factors. -/
theorem finrank_binaryProduct_rank_zero {a c : ℕ} (hc : c = 0) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear c F.Carrier)),
      Module.finrank ℂ ((T.binaryNormalizedProductFunctor a c).obj (X, Y)) =
        Module.finrank ℂ X * Module.finrank ℂ Y := by
  subst hc
  let _ := T.topology
  intro X Y
  have e : ((T.binaryNormalizedProductFunctor a 0).obj (X, Y)) ≃ₗ[ℂ] (X ⊗[ℂ] Y) :=
    (ZeroRankTensor.binaryRightZeroEquiv T a (X, Y)).toLinearEquiv.trans
      (TensorProduct.congr (LinearEquiv.refl ℂ X) ULift.moduleEquiv)
  rw [LinearEquiv.finrank_eq e, Module.finrank_tensorProduct]

/-- The dimension of a derivative depends on its order only through the order's value. -/
theorem finrank_generalLinearDerivative_order {a i : ℕ} (hi : i = a) (h : i ≤ a) :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      Module.finrank ℂ ((generalLinearDerivative T ψ a i h).obj D) =
        Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj D) := by
  subst hi
  intro D
  rfl

/-- The single grade of the top-order Leibniz filtration of `D × P`. -/
theorem finrank_topLeibnizPiece (a b : ℕ) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier))
      (x : LeibnizIndex a b (a + b)),
      Module.finrank ℂ ((leibnizPiece T ψ a b (a + b) x).obj (D, P)) =
        Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj D) *
          Module.finrank ℂ ((generalLinearDerivative T ψ b b le_rfl).obj P) := by
  let _ := T.topology
  intro D P x
  have hx := mem_leibnizIndices.mp x.property
  have h1 : x.val.1 = a := by omega
  have h2 : x.val.2 = b := by omega
  rw [leibnizPiece_obj]
  refine (finrank_generalLinearRankCast T _ _).trans ?_
  refine (finrank_binaryProduct_rank_zero T (by omega) _ _).trans ?_
  rw [finrank_generalLinearDerivative_order T ψ h1, finrank_generalLinearDerivative_order T ψ h2]

/-- The top derivative of a binary product has the product of the dimensions of the top
derivatives of its factors: the top-order Leibniz filtration has exactly one grade. -/
theorem finrank_top_binaryProduct (a b : ℕ) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Module.finrank ℂ ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
          ((T.binaryNormalizedProductFunctor a b).obj (D, P))) =
        Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj D) *
          Module.finrank ℂ ((generalLinearDerivative T ψ b b le_rfl).obj P) := by
  let _ := T.topology
  intro D P
  obtain ⟨e, s, hs⟩ := GeneralLinearDerivativeLeibnizFiltrationStatement.filtration T
    (generalLinearDerivativeLeibnizFiltration.{uF, uW} F T) ψ a b (a + b) le_rfl
  have hcard : (leibnizIndices a b (a + b)).card = 1 := by
    rw [leibnizIndices_top, Finset.card_singleton]
  let i : Fin (leibnizIndices a b (a + b)).card := e ⟨(a, b), by simp⟩
  obtain ⟨φ⟩ := hs i
  calc Module.finrank ℂ ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
          ((T.binaryNormalizedProductFunctor a b).obj (D, P)))
      = Module.finrank ℂ ((s.graded i).obj (D, P)) :=
        (finrank_graded_of_length_one s hcard i (D, P)).symm
    _ = Module.finrank ℂ ((leibnizPiece T ψ a b (a + b) (e.symm i)).obj (D, P)) :=
        (Representation.equivOfIso (φ.app (D, P))).toLinearEquiv.finrank_eq
    _ = _ := finrank_topLeibnizPiece T ψ a b D P _

end TopFinrank
/-! ## Splitting off the first factor -/

section Bridge
variable (T : F.TopologicalData)

/-- A rank-cast two-block product is the rank cast of the binary product. -/
def binaryShapeIso {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = n) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      (T.normalizedProductInductionFunctor ((BlockShape.binary a b ha hb).rankCast h)).obj
          (Fin.cases D fun _ => P) ≅
        (generalLinearRankCast T h).obj ((T.binaryNormalizedProductFunctor a b).obj (D, P)) := by
  subst h
  letI := T.topology
  intro D P
  have hf : (T.binaryPairFamilyFunctor ha hb).obj (D, P) = Fin.cases D (fun _ => P) := by
    funext i
    fin_cases i <;> rfl
  exact (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).mapIso
      (eqToIso hf.symm) ≪≫ ((T.binaryNormalizedProductPositiveIso ha hb).app (D, P)).symm

/-- A product of at least two blocks is the binary product of its lifted first
factor and the product of the remaining factors. -/
def headTailBridge {N k : ℕ} (B : BlockShape N) (h : B.length = k + 2) :
    letI := T.topology
    ∀ σ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (T.normalizedProductInductionFunctor B).obj σ ≅
        (generalLinearRankCast T (B.headRank_add_tailRank h)).obj
          ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj
            (SmoothRep.universeLift.{uF} (σ (B.headIndex h)),
              (T.normalizedProductInductionFunctor (B.tailShape h)).obj
                (fun j => σ (B.tailIndex h j)))) := by
  letI := T.topology
  intro σ
  have hf : T.headTailProductFactors B h σ =
      Fin.cases (SmoothRep.universeLift.{uF} (σ (B.headIndex h)))
        (fun _ => (T.normalizedProductInductionFunctor (B.tailShape h)).obj
          (fun j => σ (B.tailIndex h j))) := by
    funext i
    fin_cases i <;> rfl
  exact T.headTailProductInductionIso B h σ ≪≫
    (T.normalizedProductInductionFunctor (B.headTailShape h)).mapIso (eqToIso hf) ≪≫
    binaryShapeIso T (B.headRank_pos h) (B.tailRank_pos h) (B.headRank_add_tailRank h) _ _

end Bridge
/-! ## The induction step -/

section Step
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- No nonzero `P`-subrepresentation `W` of a rank-cast binary product `D × P`
has a nonzero derivative of order `level W` that embeds into the first factor `D`.
This is what Case 2 of the induction step reduces to. -/
def HeadExclusion {a b N : ℕ} (hab : a + b = N + 1)
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (P : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    Prop :=
  letI := T.topology
  ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic N F.Carrier))
    (f : W ⟶ (generalLinearRestriction T N).obj
      ((generalLinearRankCast T hab).obj ((T.binaryNormalizedProductFunctor a b).obj (D, P)))),
    Function.Injective (SmoothRep.hom f) →
    ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1), level T ψ W = k →
    ∀ (hsz : a = N + 1 - k)
      (g : (mirabolicDerivativeOfOrder T ψ N k hk).obj W ⟶ (generalLinearRankCast T hsz).obj D),
      Function.Injective (SmoothRep.hom g) →
      Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj W) → False

/-- Case 2 of the induction step is impossible: a nonzero `W` cannot inject both
into `(D × P)|P` and into `D × (P|P)`, given the head exclusion. -/
theorem caseTwo_false {m n : ℕ} (hab : m + 1 + (n + 1) = m + n + 1 + 1) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier))
      (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
      Nontrivial D → Good T ψ P → HeadExclusion T ψ hab D P →
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
        (f : W ⟶ (Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct T m n).obj (D, P))
        (g : W ⟶ (Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n).obj (D, P)),
        Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
          Nontrivial W → False := by
  let _ := T.topology
  intro D P hDne hP hX W f g hf hg hW
  have hE := Mirabolic.minusExactness.{uF, max uF uV} F T
  have hLD := leftMixedProductDerivative.{uF, max uF uV} F T
  have hτ : IsHomogeneous T ψ ((Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n).obj (D, P)) :=
    Langlands.AllFieldBZ.Derivative.RightMixedLevel.isHomogeneous_mirabolicRankCast T ψ _ _
      (leftMixedProductHomogeneity.{uF, max uF uV} F T ψ (m + 1) n D _ hP.1)
  have h4 := level_of_good T ψ P hP
  have hlevτ : level T ψ ((Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n).obj (D, P)) = n + 1 :=
    (Langlands.AllFieldBZ.Derivative.LevelCalculus.level_mirabolicRankCast T ψ (show (m + 1) + n = m + n + 1 by omega)
      ((T.leftMixedProductFunctor (m + 1) n).obj
        (D, (generalLinearRestriction T n).obj P))).trans
      (le_antisymm ((Langlands.AllFieldBZ.Derivative.RestrictedProductLevel.level_leftMixed_le T ψ hLD D _).trans h4.le)
        (h4.symm.le.trans (Langlands.AllFieldBZ.Derivative.RestrictedProductLevel.le_level_leftMixed T ψ hLD D _ hDne)))
  have hlevW : level T ψ W = n + 1 := (Langlands.AllFieldBZ.Derivative.LevelCalculus.level_eq_of_isHomogeneous T ψ hτ g hg hW).trans hlevτ
  have hk : 0 < n + 1 ∧ n + 1 ≤ m + n + 1 + 1 := ⟨Nat.succ_pos n, by omega⟩
  have hWk : Nontrivial ((mirabolicDerivativeOfOrder T ψ (m + n + 1) (n + 1) hk).obj W) := by
    obtain ⟨-, ⟨_, h⟩, -⟩ := (level_eq_iff T ψ (Nat.succ_pos n) W).mp hlevW
    exact h
  have hi : 0 < n + 1 ∧ n + 1 ≤ n + 1 := ⟨Nat.succ_pos n, le_rfl⟩
  have hV : Module.finrank ℂ ((mirabolicDerivativeOfOrder T ψ n (n + 1) hi).obj
      ((generalLinearRestriction T n).obj P)) = 1 := by
    rw [← RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ le_rfl hi P]
    exact hP.2
  have hsz : m + 1 = m + n + 1 + 1 - (n + 1) := by omega
  obtain ⟨g', hg'⟩ := exists_injective_of_rankCast T
    (show m + 1 + n + 1 - (n + 1) = m + n + 1 + 1 - (n + 1) by omega)
    (show m + 1 + n + 1 - (n + 1) = m + 1 + (n + 1 - (n + 1)) by omega)
    (show m + 1 = m + 1 + (n + 1 - (n + 1)) by omega) hsz
    ((mirabolicDerivativeOfOrder T ψ (m + n + 1) (n + 1) hk).map g)
    (map_injective_of_exact (Langlands.AllFieldBZ.Derivative.LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder T ψ hE _ _ hk) g hg)
    (mirabolicDerivativeOfOrder_rankCast_obj T ψ (show (m + 1) + n = m + n + 1 by omega)
      (n + 1) hk ⟨Nat.succ_pos n, by omega⟩ (by omega)
      ((T.leftMixedProductFunctor (m + 1) n).obj (D, (generalLinearRestriction T n).obj P)))
    ((hLD.1 ψ (m + 1) n (n + 1) hi).some.app (D, (generalLinearRestriction T n).obj P) ≪≫
      binaryLineIso T (Nat.sub_self (n + 1)) (by omega) D _ hV)
  exact hX W f hf (n + 1) hk hlevW hsz g' hg' hWk

/-- The binary step: if `D` is irreducible supercuspidal and the tail `P` is good,
then `D × P` is good, provided Case 2 is excluded. -/
theorem good_step {a b N : ℕ} (hab : a + b = N + 1) (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      D.IsIrreducible → IsSupercuspidal D.representation →
      (∀ n (hn : b = n + 1), Good T ψ ((generalLinearRankCast T hn).obj P)) →
      HeadExclusion T ψ hab D P →
      Good T ψ ((generalLinearRankCast T hab).obj
        ((T.binaryNormalizedProductFunctor a b).obj (D, P))) := by
  let _ := T.topology
  intro D P hirr hsc hP hX
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  obtain rfl : N = m + n + 1 := by omega
  have hP' : Good T ψ P := hP n rfl
  have hY := leftMixedProductHomogeneity.{uF, max uF uV} F T ψ 0 n
    ((mirabolicDerivative T ψ 0 m).obj ((mirabolicRankCast T (show m = 0 + m by omega)).obj
      ((generalLinearRestriction T m).obj D))) ((generalLinearRestriction T n).obj P) hP'.1
  have hD := rightMixedProductPhiMinusDetection.{uF, max uF uV} F T
  have hC := mirabolicProductMinusCompatibility.{uF, max uF uV} F T
  have hS : MirabolicProductMinus.RightPhiShortExact.{uF, max uF uV} F T := hC.2.2.2.2.1
  have hB : MirabolicProductMinus.RightPhiBoundary.{uF, max uF uV} F T := hC.2.2.2.2.2
  have hR := mirabolicProductRestriction.{uF, max uF uV} F T
  have hLD := leftMixedProductDerivative.{uF, max uF uV} F T
  have hE := Mirabolic.minusExactness.{uF, max uF uV} F T
  have hDj := hasNonzeroDerivative_eq_of_supercuspidal T ψ D hirr hsc
  have hC2 := caseTwo_false T ψ hab D P (nontrivial_of_isIrreducible D.representation hirr) hP' hX
  have hH := Langlands.AllFieldBZ.Derivative.RestrictedProductLevel.isHomogeneous_restrictedProduct T ψ hE hD hS hB hR hLD m n 0 m (by omega) D P hDj hY
  have hH' : IsHomogeneous T ψ ((Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct T m n).obj (D, P)) := hH hC2
  refine ⟨hH', ?_⟩
  rw [finrank_generalLinearRankCast_top T ψ hab,
    finrank_top_binaryProduct T ψ,
    (Classification.supercuspidalDerivatives.{uF, max uF uV} F T ψ m D hirr hsc).2, hP'.2]

end Step
/-! ## One block -/

section Single
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A one-block family is the transport of its unique factor. -/
theorem singleFamily_eq {n : ℕ} (B : BlockShape n) (h : B.length = 1)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun j => ((B.singleBlock_size h j).symm ▸
      ((B.singleBlock_size h (B.singleBlockIndex h)) ▸ σ (B.singleBlockIndex h)) :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size j) F.Carrier))) = σ := by
  let := T.topology
  funext j
  have hj := B.eq_singleBlockIndex h j
  subst j
  exact transport_symm_cancel
    (fun r => SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) _ _

/-- A one-block product of a transported factor is the carrier lift of that factor. -/
def singletonProductLiftIso {r : ℕ} (C : BlockShape r) (hC : C.length = 1)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor C).obj
      (fun j => (C.singleBlock_size hC j).symm ▸ A)) ≅
      SmoothRep.universeLift.{uF} A :=
  letI := T.topology
  SmoothRep.mkIso (Parabolic.equivTrans
    (T.normalizedProductInductionObjEquiv C
      (fun j => (C.singleBlock_size hC j).symm ▸ A))
    (Parabolic.equivTrans (T.singleBlockTransportedProductEquiv C hC A)
      (SmoothRep.universeLiftEquiv.{uF} A)))

theorem supercuspidalProperty_transport {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      supercuspidalProperty X →
        supercuspidalProperty (h ▸ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) := by
  subst h
  intro X hX
  exact hX

/-- The base case: a product of one irreducible supercuspidal block is good. -/
theorem good_single {n : ℕ} (B : BlockShape (n + 1)) (hB : B.length = 1) :
    letI := T.topology
    ∀ A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i),
      Good T ψ ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)) := by
  let _ := T.topology
  intro A
  let X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) :=
    (B.singleBlock_size hB (B.singleBlockIndex hB)) ▸ (A (B.singleBlockIndex hB)).obj
  have hX : supercuspidalProperty X :=
    supercuspidalProperty_transport T _ _ (A (B.singleBlockIndex hB)).property
  let e : (T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj) ≅
      SmoothRep.universeLift.{uF} X :=
    (T.normalizedProductInductionFunctor B).mapIso
      (eqToIso (singleFamily_eq T B hB (fun i => (A i).obj)).symm) ≪≫
    singletonProductLiftIso T B hB X
  exact good_of_iso T ψ e.symm (good_universeLift_of_supercuspidal T ψ X hX)

end Single
/-! ## Induction on the number of blocks -/

section Induction
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The ordering hypothesis of BZ77 Theorem 4.11: `A j ≇ ν A i` whenever `i < j`. -/
def Ordered {r : ℕ} (B : BlockShape r) :
    letI := T.topology
    (∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)) → Prop :=
  letI := T.topology
  fun A => ∀ i j : Fin B.length, i < j →
    (⟨B.size j, (A j).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩

/-- Case 2 is excluded for the split of an ordered product into its first
factor and the product of the others. -/
theorem headExclusion_of_ordered {n k : ℕ} (B : BlockShape (n + 1)) (h : B.length = k + 2) :
    letI := T.topology
    ∀ A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i),
      Ordered T B A →
      HeadExclusion T ψ (B.headRank_add_tailRank h)
        (SmoothRep.universeLift.{uF} (A (B.headIndex h)).obj)
        ((T.normalizedProductInductionFunctor (B.tailShape h)).obj
          (fun j => (A (B.tailIndex h j)).obj)) := by
  let _ := T.topology
  intro A hA W f hf k' hk hlev hsz g hg hW
  let e := headTailBridge T B h (fun i => (A i).obj)
  refine OrderedCuspidalProductHeadShift.headShift_false F T ψ B A (B.headIndex h) ?_ W
    (f ≫ (generalLinearRestriction T n).map e.inv)
    ((iso_hom_injective ((generalLinearRestriction T n).mapIso e.symm)).comp hf)
    k' hk hlev hsz g hg hW
  intro j hj
  refine hA (B.headIndex h) j ?_
  rw [Fin.lt_def]
  have : j.val ≠ (B.headIndex h).val := fun h' => hj (Fin.ext h')
  simp only [BlockShape.headIndex, Fin.val_cast, Fin.val_zero] at this ⊢
  omega

theorem ordered_tail {n k : ℕ} (B : BlockShape (n + 1)) (h : B.length = k + 2) :
    letI := T.topology
    ∀ A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i),
      Ordered T B A → Ordered T (B.tailShape h) (fun j => A (B.tailIndex h j)) := by
  let _ := T.topology
  intro A hA i j hij
  refine hA (B.tailIndex h i) (B.tailIndex h j) ?_
  rw [Fin.lt_def] at hij ⊢
  simp only [BlockShape.tailIndex, Fin.val_cast, Fin.val_succ]
  omega

/-- Ordered products of irreducible supercuspidal blocks are good. -/
theorem good_product (l : ℕ) :
    letI := T.topology
    ∀ {r : ℕ} (B : BlockShape r), B.length = l + 1 →
    ∀ (A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
      Ordered T B A → ∀ n (hr : r = n + 1),
        Good T ψ ((generalLinearRankCast T hr).obj
          ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj))) := by
  let _ := T.topology
  induction l with
  | zero =>
    intro r B hB A _ n hr
    subst hr
    exact good_single T ψ B hB A
  | succ k ih =>
    intro r B hB A hA n hr
    subst hr
    have h : B.length = k + 2 := hB
    have hT := ih (B.tailShape h) rfl (fun j => A (B.tailIndex h j)) (ordered_tail T B h A hA)
    let e := headTailBridge T B h (fun i => (A i).obj)
    refine good_of_iso T ψ e.symm (good_step T ψ (B.headRank_add_tailRank h)
      (B.headRank_pos h) (B.tailRank_pos h) _ _ ?_ ?_ hT
      (headExclusion_of_ordered T ψ B h A hA))
    · exact (SmoothRep.isIrreducible_universeLift_iff _).mpr (A (B.headIndex h)).property.1
    · exact isSupercuspidal_of_equiv (SmoothRep.universeLiftEquiv.{uF} _)
        (A (B.headIndex h)).property.2

end Induction
end OrderedCuspidalProductNondegeneracy
open OrderedCuspidalProductNondegeneracy in
/-- **BZ77 Theorem 4.11** (sufficient direction). If `A j ≇ ν A i` whenever
`i < j`, every nonzero subrepresentation of the restriction to `P_(N+1)` of the
normalized product `A_1 × ⋯ × A_r` has nonzero top derivative. -/
theorem orderedCuspidalProductNoDegenerateSubmodules (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    OrderedCuspidalProductNoDegenerateSubmodules.{uF, uV} F T := by
  let _ := T.topology
  intro ψ N B A hA U hU
  obtain ⟨l, hl⟩ : ∃ l, B.length = l + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    have hempty : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
    have hn0 : N + 1 = 0 := by simpa using B.sum_eq.symm
    omega
  exact Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_subrepresentation_of_good T ψ _ (Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_product T ψ l B hl A hA N rfl) U hU

end Langlands.AllFieldBZ.Derivative
