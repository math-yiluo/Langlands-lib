import Langlands.Global.AdelicHarishChandraDecomposition
import Langlands.Global.AdelicStandardConstantTermOperator

/-! # Harish-Chandra decomposition of weighted `L²` by constant-term operators

For a weight `W` invariant under `P₀(F)` and the standard unipotent radicals, the folded constant
terms are contractions `T S` of `L²((Haar|_{D₀}).withDensity W)`, the one for `S = Δ₀` is the
identity, and the components `Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S` sum to the identity and have norm at
most `2^{|P|}`. -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.HarishChandraDecomposition

section Operators

variable {α : Type v} [DecidableEq α] {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The alternating sum of contractions over the subsets of `P` has norm at most `2^{|P|}`. -/
theorem norm_alternatingSum_le (T : Finset α → E →L[ℂ] E) (hT : ∀ S, ‖T S‖ ≤ 1)
    (P : Finset α) : ‖alternatingSum T P‖ ≤ 2 ^ P.card := by
  unfold alternatingSum
  calc ‖∑ S ∈ P.powerset, ((-1 : ℂ) ^ (P \ S).card) • T S‖
      ≤ ∑ S ∈ P.powerset, ‖((-1 : ℂ) ^ (P \ S).card) • T S‖ := norm_sum_le _ _
    _ ≤ ∑ _S ∈ P.powerset, (1 : ℝ) := Finset.sum_le_sum fun S _ => by
        rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hT S
    _ = 2 ^ P.card := by simp [Finset.card_powerset]

/-- If `T D = id`, every vector is bounded by the sum of the norms of its components. -/
theorem norm_le_sum_norm_alternatingSum (T : Finset α → E →L[ℂ] E) (D : Finset α)
    (hD : T D = ContinuousLinearMap.id ℂ E) (x : E) :
    ‖x‖ ≤ ∑ P ∈ D.powerset, ‖alternatingSum T P x‖ := by
  have h : ∑ P ∈ D.powerset, alternatingSum T P = ContinuousLinearMap.id ℂ E := by
    rw [sum_alternatingSum, hD]
  calc ‖x‖ = ‖(∑ P ∈ D.powerset, alternatingSum T P) x‖ := by rw [h]; rfl
    _ = ‖∑ P ∈ D.powerset, alternatingSum T P x‖ := by rw [sum_apply]
    _ ≤ _ := norm_sum_le _ _

end Operators

end Langlands.Global.HarishChandraDecomposition

namespace Langlands.Global.StandardParabolicFamily

open scoped CategoryTheory.MonObj
open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm
open Classical

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Λ₀" => minimalParabolicImage F G 𝓕.i 𝓕.ν
local notation "D₀" => LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
  (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν)
local notation "hD₀" => LeftCosetSpace.fundamentalDomain_unique (minimalParabolicImage F G 𝓕.i 𝓕.ν)
  (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν)

/-- The weighted measure `W · (Haar restricted to the fundamental domain of P₀(F))`. -/
abbrev weightedHaar (W : AdelicGroupPoints F G → ℝ≥0∞) : Measure (AdelicGroupPoints F G) :=
  ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict D₀).withDensity W

/-- The standard unipotent subgroup of all simple roots has only the trivial adelic point. -/
theorem coe_eq_one_of_mem_top
    (v : adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)) :
    (v : AdelicGroupPoints F G) = 1 := by
  obtain ⟨y, hy⟩ := v
  have hJ : (𝓕.finsetIndex 𝓕.simpleRootFinset).1 = simpleRelativeRoots 𝓕.i 𝓕.ν :=
    congrArg Subtype.val 𝓕.finsetIndex_simpleRootFinset
  change y ∈ (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1).carrier _ at hy
  rw [hJ, standardUnipotent_simple_eq_bot] at hy
  exact Subgroup.mem_bot.mp hy

/-- On the fundamental domain, the folded constant term along `U_{Δ₀} = 1` is the identity. -/
theorem foldConstantTerm_top_of_mem (f : AdelicGroupPoints F G → ℂ) {g : AdelicGroupPoints F G}
    (hg : g ∈ D₀) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν
      (𝓕.finsetIndex 𝓕.simpleRootFinset).1
    haveI : LocallyCompactSpace (adelicPoints F G
        (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)) :=
      hcl.locallyCompactSpace
    foldConstantTerm Λ₀ D₀ hD₀
      (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)).subtype
      Measure.haar (ConstantTermAverage.rationalFundamentalDomain F G
        (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)) f g = f g := by
  set J := (𝓕.finsetIndex 𝓕.simpleRootFinset).1 with hJdef
  let hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J)) :=
    hcl.locallyCompactSpace
  let : CompactSpace (RationalQuotient F G (standardUnipotent 𝓕.i 𝓕.ν J)) :=
    compactSpace_standardUnipotent F G 𝓕.i 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic J
      (𝓕.finsetIndex 𝓕.simpleRootFinset).2
  have hne : ((Measure.haar : Measure (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J)))
      (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent 𝓕.i 𝓕.ν J))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_zero _,
      Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_top _⟩
  unfold foldConstantTerm
  have hint : ∀ v : adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J),
      f (fold Λ₀ hD₀ ((adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J)).subtype v * g)) =
        f (fold Λ₀ hD₀ g) := fun v => by
    rw [Subgroup.coe_subtype, 𝓕.coe_eq_one_of_mem_top v, one_mul]
  simp_rw [hint]
  rw [setIntegral_const, measureReal_def, smul_smul, inv_mul_cancel₀ hne, one_smul,
    fold_of_mem Λ₀ hD₀ hg]

/-- **Constant-term operators on weighted `L²`.** For a measurable weight `W` invariant under
`P₀(F)` and under every `U_J(𝔸)` on the left, there are contractions `T S` of
`L²(weightedHaar W)`, one for each finset `S`, computing the folded constant term along
`U_{S ∩ Δ₀}` on measurable representatives, with `T Δ₀ = id`. -/
theorem exists_componentOperators (W : AdelicGroupPoints F G → ℝ≥0∞) (hW : Measurable W)
    (hWΛ : ∀ l ∈ Λ₀, ∀ x, W (l * x) = W x)
    (hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x) :
    ∃ T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)),
      (∀ S, ‖T S‖ ≤ 1) ∧
      (∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn →
        haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1
        haveI : LocallyCompactSpace (adelicPoints F G
            (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) := hcl.locallyCompactSpace
        T S Fn =ᵐ[𝓕.weightedHaar W] foldConstantTerm Λ₀ D₀ hD₀
          (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)).subtype Measure.haar
          (ConstantTermAverage.rationalFundamentalDomain F G
            (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) f) ∧
      T 𝓕.simpleRootFinset = ContinuousLinearMap.id ℂ _ := by
  choose T hT using fun S : Finset (characterLattice 𝓕.T) =>
    standardConstantTermOperator F G 𝓕.T 𝓕.i 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic
      (𝓕.finsetIndex S).1 (𝓕.finsetIndex S).2 W hW hWΛ (hWU _ (𝓕.finsetIndex S).2)
  refine ⟨T, fun S => (hT S).1, fun S Fn f hf hfF => (hT S).2 Fn hf hfF, ?_⟩
  ext1 Fn
  have hm := Lp.aestronglyMeasurable Fn
  have h1 := (hT 𝓕.simpleRootFinset).2 Fn hm.stronglyMeasurable_mk.measurable hm.ae_eq_mk.symm
  have hDm : MeasurableSet D₀ := LeftCosetSpace.measurableSet_fundamentalDomain _
    (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν)
  have hmem : ∀ᵐ g ∂(𝓕.weightedHaar W), g ∈ D₀ :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hDm)
  let hclt := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν
    (𝓕.finsetIndex 𝓕.simpleRootFinset).1
  let : LocallyCompactSpace (adelicPoints F G
      (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)) :=
    hclt.locallyCompactSpace
  have h2 : (foldConstantTerm Λ₀ D₀ hD₀
      (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)).subtype
      Measure.haar (ConstantTermAverage.rationalFundamentalDomain F G
        (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex 𝓕.simpleRootFinset).1)) (hm.mk Fn))
        =ᵐ[𝓕.weightedHaar W] hm.mk Fn :=
    hmem.mono fun g hg => 𝓕.foldConstantTerm_top_of_mem _ hg
  exact Lp.ext (h1.trans (h2.trans hm.ae_eq_mk.symm))

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open scoped CategoryTheory.MonObj
open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm
open Classical

/-- **Statement form.** For a compatible standard parabolic family and a measurable weight `W`
invariant on the left under `P₀(F)` and under every `U_J(𝔸)`, there are contractions `T S` of
`L²((Haar|_{D₀}).withDensity W)` computing the folded constant terms along `U_{S ∩ Δ₀}` on
measurable representatives. Their Harish-Chandra components `Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S`
sum to the identity over `P ⊆ Δ₀`, and each has norm at most `2^{|P|}`. -/
def L2HarishChandraDecompositionStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (W : AdelicGroupPoints F G → ℝ≥0∞), Measurable W →
    (∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x) →
    (∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x) →
    ∃ T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)),
      (∀ S, ‖T S‖ ≤ 1) ∧
      (∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn →
        haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1
        haveI : LocallyCompactSpace (adelicPoints F G
            (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) := hcl.locallyCompactSpace
        T S Fn =ᵐ[𝓕.weightedHaar W] foldConstantTerm (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
            (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
          (LeftCosetSpace.fundamentalDomain_unique (minimalParabolicImage F G 𝓕.i 𝓕.ν)
            (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
          (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)).subtype Measure.haar
          (ConstantTermAverage.rationalFundamentalDomain F G
            (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) f) ∧
      (∑ P ∈ 𝓕.simpleRootFinset.powerset, alternatingSum T P = ContinuousLinearMap.id ℂ _) ∧
      ∀ P, ‖alternatingSum T P‖ ≤ 2 ^ P.card

/-- Proof of `L2HarishChandraDecompositionStatement`. -/
theorem l2HarishChandraDecomposition : L2HarishChandraDecompositionStatement.{u} := by
  intro F _ _ G _ _ _ 𝓕 W hW hWΛ hWU
  obtain ⟨T, hT1, hT2, hT3⟩ := 𝓕.exists_componentOperators W hW hWΛ hWU
  exact ⟨T, hT1, hT2, by rw [sum_alternatingSum, hT3], fun P => norm_alternatingSum_le T hT1 P⟩

end Langlands.Global
