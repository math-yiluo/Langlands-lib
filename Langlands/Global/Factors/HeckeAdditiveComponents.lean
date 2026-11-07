import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.Factors.HeckeFunctionalEquationStatement
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof

/-! # Actual additive restrictions and their finite integral support -/

noncomputable section

open Filter Topology
open scoped RestrictedProduct

namespace Langlands.Global.HeckeFunctionalEquation

universe u v

/-- A continuous additive character of a product has trivial single factors
outside a finite set. -/
theorem exists_finset_trivial_single {ι : Type u} {G : ι → Type v}
    [DecidableEq ι] [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    (θ : AddChar (∀ i, G i) Circle) (hθ : Continuous θ) :
    ∃ S : Finset ι, ∀ i ∉ S, ∀ x : G i, θ (Pi.single i x) = 1 := by
  classical
  let U : Set (∀ i, G i) := {x | ‖(θ x : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hU : U ∈ 𝓝 (0 : ∀ i, G i) := by
    apply (isOpen_lt ((continuous_subtype_val.comp hθ).sub
      continuous_const).norm continuous_const).mem_nhds
    change ‖(θ 0 : ℂ) - 1‖ < (1 / 2 : ℝ)
    simp
  simp only [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, t, ht, hSU⟩ := hU
  refine ⟨S, fun i hi x => ?_⟩
  apply Subtype.ext
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hx : Pi.single i (n • x) ∈ U := by
    apply hSU
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simpa only [Pi.single_eq_of_ne hji, Pi.zero_apply] using mem_of_mem_nhds (ht j)
  change ‖(θ (Pi.single i (n • x)) : ℂ) - 1‖ < (1 / 2 : ℝ) at hx
  simpa only [Pi.single_nsmul, AddChar.map_nsmul_eq_pow, Circle.coe_pow] using hx

variable (K : Type u) [Field K] [NumberField K]

local instance : DecidableEq (FinitePlace K) := Classical.decEq _
local instance : DecidableEq (InfinitePlace K) := Classical.decEq _

/-- Insert one additive finite coordinate, with zero at every other place. -/
def finiteAdditiveInclusion (v : FinitePlace K) : FiniteCompletion K v →+ Adeles K :=
  (0 : FiniteCompletion K v →+ InfiniteAdeles K).prod
    (RestrictedProduct.singleAddMonoidHom (fun w : FinitePlace K =>
      w.adicCompletionIntegers K) v)

theorem continuous_finiteAdditiveInclusion (v : FinitePlace K) :
    Continuous (finiteAdditiveInclusion K v) := by
  let S : Set (FinitePlace K) := {v}ᶜ
  let f : FiniteCompletion K v →
      Πʳ w : FinitePlace K, [FiniteCompletion K w, w.adicCompletionIntegers K]_[Filter.principal S] :=
    fun x => ⟨Pi.single v x, fun w hw => by
      have h : w ≠ v := by simpa [S] using hw
      simp [Pi.single_eq_of_ne h]⟩
  have hf : Continuous f :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  have hS : Filter.cofinite ≤ Filter.principal S := by simp [S]
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

/-- Insert one additive infinite coordinate, with zero at every other place. -/
def infiniteAdditiveInclusion (v : InfinitePlace K) : InfiniteCompletion K v →+ Adeles K :=
  (AddMonoidHom.single (fun w : InfinitePlace K => InfiniteCompletion K w) v).prod 0

theorem continuous_infiniteAdditiveInclusion (v : InfinitePlace K) :
    Continuous (infiniteAdditiveInclusion K v) :=
  (continuous_single v).prodMk continuous_const

/-- Include the product of all completed integer rings in the full adeles. -/
def integralAdditiveInclusion :
    (∀ v : FinitePlace K, v.adicCompletionIntegers K) →+ Adeles K :=
  (0 : (∀ v : FinitePlace K, v.adicCompletionIntegers K) →+ InfiniteAdeles K).prod
    (integralProductMap K).toAddMonoidHom

theorem continuous_integralAdditiveInclusion : Continuous (integralAdditiveInclusion K) :=
  continuous_const.prodMk (continuous_integralProductMap K)

theorem integralAdditiveInclusion_single (v : FinitePlace K)
    (x : v.adicCompletionIntegers K) :
    integralAdditiveInclusion K (Pi.single v x) = finiteAdditiveInclusion K v x := by
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change ((Pi.single v x : ∀ w : FinitePlace K, w.adicCompletionIntegers K) w :
        FiniteCompletion K w) =
      (Pi.single v (x : FiniteCompletion K v) : ∀ w : FinitePlace K, FiniteCompletion K w) w
    by_cases h : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne h]

variable {K}

/-- The finite restriction as an additive character; nontriviality is a separate
arithmetic obligation. -/
def finiteAdditiveRestriction (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (v : FinitePlace K) : AddChar (FiniteCompletion K v) Circle :=
  ψ.toAddChar.compAddMonoidHom (finiteAdditiveInclusion K v)

theorem continuous_finiteAdditiveRestriction
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) (v : FinitePlace K) :
    Continuous (finiteAdditiveRestriction ψ v) :=
  ψ.continuous_toFun.comp (continuous_finiteAdditiveInclusion K v)

/-- The actual nontrivial finite restriction, in the topology used by the target. -/
def finiteAdditiveComponent (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (v : FinitePlace K) (h : finiteAdditiveRestriction ψ v ≠ 1) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
      (CompletionPadic.topologicalData v).topology where
  toAddChar := finiteAdditiveRestriction ψ v
  continuous_toFun := continuous_finiteAdditiveRestriction ψ v
  nontrivial := h

theorem isFiniteAdditiveComponent_finiteAdditiveComponent
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) (v : FinitePlace K)
    (h : finiteAdditiveRestriction ψ v ≠ 1) :
    IsFiniteAdditiveComponent ψ v (finiteAdditiveComponent ψ v h) := by
  intro x
  rfl

/-- Every nontrivial actual finite restriction admits the target's self-dual Haar
measure, by the published p-adic existence theorem. -/
theorem nonempty_selfDualHaar_of_nontrivial_restriction
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) (v : FinitePlace K)
    (h : finiteAdditiveRestriction ψ v ≠ 1) :
    Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v)
      (finiteAdditiveComponent ψ v h)) := by
  let F := CompletionPadic.padicField v
  let T := CompletionPadic.topologicalData v
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  obtain ⟨htd, hμ⟩ := HarmonicAnalysis.padicSelfDualMeasureExists F T
  let := htd
  obtain ⟨μ, hμ⟩ := hμ (finiteAdditiveComponent ψ v h)
  exact ⟨⟨μ, hμ⟩⟩

/-- At almost all finite places, the restriction is trivial on the completed
integer ring. This uses continuity alone, with no diagonal-triviality premise. -/
theorem exists_finset_integral_restriction_eq_one
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ x : v.adicCompletionIntegers K,
      finiteAdditiveRestriction ψ v x = 1 := by
  let θ := ψ.toAddChar.compAddMonoidHom (integralAdditiveInclusion K)
  have hθ : Continuous θ := ψ.continuous_toFun.comp (continuous_integralAdditiveInclusion K)
  obtain ⟨S, hS⟩ := exists_finset_trivial_single θ hθ
  refine ⟨S, fun v hv x => ?_⟩
  have h := hS v hv x
  change ψ (integralAdditiveInclusion K (Pi.single v x)) = 1 at h
  rw [integralAdditiveInclusion_single] at h
  exact h

end Langlands.Global.HeckeFunctionalEquation
