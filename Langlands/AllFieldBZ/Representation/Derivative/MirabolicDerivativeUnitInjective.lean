import Langlands.AllFieldBZ.Representation.Derivative.LevelCalculus
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicSmoothPhiPlusIterate
import Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff hasNonzeroDerivative_of_isHomogeneous isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeAdjunction mirabolicDerivativeAdjunction_comp_left mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrderAdjunction mirabolicDerivativeOfOrderAdjunction_comp_left mirabolicDerivativeOfOrderAdjunction_unit mirabolicDerivativeOfOrderAdjunction_unit_comp mirabolicDerivativeOfOrderRightAdjoint mirabolicDerivativeOfOrderUnit mirabolicDerivativeOfOrderUnitKer mirabolicDerivativeOfOrderUnit_injective mirabolicDerivativeOfOrderUnit_injective_of_forall mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp mirabolicDerivativeOfOrder_map_injective mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivativeRightAdjoint mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastHomEquiv mirabolicRankCastHomEquiv_comp_left mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiHatPlusIterate phiHatPlusIterateAdjunction phiHatPlusIterateAdjunction_comp_left phiHatPlusIterateAdjunction_succ phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero subsingleton_mirabolicDerivativeOfOrder_unit_ker
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uA uV uF

variable {F : LocalFieldPackage.{uF}}

/-! ## Derivatives preserve injections -/

/-- The order-`l` derivative carries injective intertwiners to injective intertwiners. -/
theorem mirabolicDerivativeOfOrder_map_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective (SmoothRep.hom ((mirabolicDerivativeOfOrder T ψ N l hl).map f)) := by
  let := T.topology
  intro A B f hf
  exact LevelCalculus.map_injective_of_exact
    (LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder T ψ
      (Mirabolic.minusExactness.{uF, uV} F T) N l hl) f hf

/-! ## Zelevinsky 5.1 (1) ⇒ (3): injectivity of the unit -/

/-- The kernel of the unit `A → Y(A^(l))`, as a smooth subrepresentation of `A`: the
source's `Ker A`. -/
def mirabolicDerivativeOfOrderUnitKer (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) →
      SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier) :=
  letI := T.topology
  fun A => SmoothRep.subrepresentation A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker

/-- The kernel of the unit `A → Y(A^(l))` has zero order-`l` derivative. -/
theorem subsingleton_mirabolicDerivativeOfOrder_unit_ker (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Subsingleton ((mirabolicDerivativeOfOrder T ψ N l hl).obj
        (mirabolicDerivativeOfOrderUnitKer T ψ N l hl A)) := by
  let := T.topology
  intro A
  change Subsingleton ((mirabolicDerivativeOfOrder T ψ N l hl).obj
    (SmoothRep.subrepresentation A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker))
  have hcomp : (mirabolicDerivativeOfOrderUnit T ψ N l hl A).comp
      (SmoothRep.hom (SmoothRep.subtype A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker)) =
        0 := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact x.2
  have h0 := mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp T ψ N l hl _ hcomp
  have hinj := mirabolicDerivativeOfOrder_map_injective T ψ N l hl
    (SmoothRep.subtype A (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker)
    (SmoothRep.subtype_injective A _)
  refine ⟨fun x y => hinj ?_⟩
  rw [h0]
  rfl

/-- If every nonzero invariant subspace of `A` has a nonzero order-`l` derivative, the unit
`A → Y(A^(l))` is injective. -/
theorem mirabolicDerivativeOfOrderUnit_injective_of_forall (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ U : Subrepresentation A.representation, U ≠ ⊥ →
        HasNonzeroDerivative T ψ (SmoothRep.subrepresentation A U) l) →
      Function.Injective (mirabolicDerivativeOfOrderUnit T ψ N l hl A) := by
  let := T.topology
  intro A h
  have hK : (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker = ⊥ := by
    by_contra hne
    obtain ⟨_, hn⟩ := h _ hne
    exact (not_nontrivial_iff_subsingleton.mpr
      (subsingleton_mirabolicDerivativeOfOrder_unit_ker T ψ N l hl A)) hn
  intro x y hxy
  have hmem : x - y ∈ (mirabolicDerivativeOfOrderUnit T ψ N l hl A).ker := by
    change mirabolicDerivativeOfOrderUnit T ψ N l hl A (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [hK] at hmem
  exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem)

/-- Zelevinsky 1980, 5.1 (1) ⇒ (3): for `A` homogeneous of level `l`, the unit
`A → Y(A^(l))` is injective. -/
theorem mirabolicDerivativeOfOrderUnit_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N l : ℕ) (hl : 0 < l ∧ l ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      IsHomogeneous T ψ A → level T ψ A = l →
        Function.Injective (mirabolicDerivativeOfOrderUnit T ψ N l hl A) := by
  let := T.topology
  intro A hA hlev
  apply mirabolicDerivativeOfOrderUnit_injective_of_forall T ψ N l hl A
  intro U hU
  have h := hA U hU
  have hne : level T ψ (SmoothRep.subrepresentation A U) ≠ 0 := by
    rw [h, hlev]
    exact hl.1.ne'
  have hd := LevelCalculus.hasNonzeroDerivative_level T ψ _ hne
  rwa [h, hlev] at hd

/-- In a homogeneous representation of level `l > 0`, the source of every injective
intertwiner from a nonzero representation has a nonzero order-`l` derivative and no nonzero
derivative of higher order. -/
theorem hasNonzeroDerivative_of_isHomogeneous (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N l : ℕ} (hl : 0 < l) :
    letI := T.topology
    ∀ {W X : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)}, IsHomogeneous T ψ X →
      level T ψ X = l → ∀ (f : W ⟶ X), Function.Injective (SmoothRep.hom f) → Nontrivial W →
        HasNonzeroDerivative T ψ W l ∧ ∀ j, l < j → ¬ HasNonzeroDerivative T ψ W j := by
  let := T.topology
  intro W X hX hlev f hf hW
  have hW' : level T ψ W = l :=
    (LevelCalculus.level_eq_of_isHomogeneous T ψ hX f hf hW).trans hlev
  refine ⟨?_, fun j hj hd => ?_⟩
  · have hd := LevelCalculus.hasNonzeroDerivative_level T ψ W (by omega)
    rwa [hW'] at hd
  · have := le_level_of_hasNonzeroDerivative T ψ W hd
    omega

/-! ## Zelevinsky 5.1 (3) ⇒ (1): homogeneity from an embedding into `Y` -/

/-! ## Zelevinsky 5.1 (1) ⇔ (3) -/

end Langlands.AllFieldBZ.Derivative
