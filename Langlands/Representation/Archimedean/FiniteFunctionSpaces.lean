import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-dimensional spaces of functions: evaluation points and derivatives of families

* `exists_finset_eval_injective`: a finite-dimensional space `V` of functions `X → ℂ` has a
  finite set `T` of at most `dim V` points on which evaluation is injective.
* `mem_of_hasDerivAt`: if `t ↦ F t` is a family in `V` and `t ↦ F t x` has derivative `F' x` at
  `0` for every `x`, then `F' ∈ V` (finite-dimensional subspaces are closed in the topology of
  pointwise convergence).
-/

noncomputable section

open Topology

set_option autoImplicit false

namespace Langlands.Archimedean.FiniteFunctionSpaces

variable {X : Type*}

/-- **Unisolvent points.** -/
theorem exists_finset_eval_injective :
    ∀ (r : ℕ) (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V], Module.finrank ℂ V = r →
      ∃ T : Finset X, T.card ≤ r ∧ ∀ f ∈ V, (∀ x ∈ T, f x = 0) → f = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro V _ hr
    classical
    by_cases hV : V = ⊥
    · exact ⟨∅, by simp, fun f hf _ => by rw [hV] at hf; exact (Submodule.mem_bot ℂ).1 hf⟩
    obtain ⟨f₀, hf₀, hf₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, f₀ x₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf₀0 (funext h)
    let V' : Submodule ℂ (X → ℂ) := V ⊓ LinearMap.ker (LinearMap.proj x₀)
    have hlt : V' < V := by
      refine lt_of_le_of_ne inf_le_left fun heq => hx₀ ?_
      have : f₀ ∈ V' := heq ▸ hf₀
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2
    have hrank : Module.finrank ℂ V' < r := hr ▸ Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨T', hT'c, hT'⟩ := ih _ hrank V' rfl
    refine ⟨insert x₀ T', ?_, fun f hf h0 => ?_⟩
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · refine hT' f (Submodule.mem_inf.2 ⟨hf, LinearMap.mem_ker.2 ?_⟩) fun x hx =>
        h0 x (Finset.mem_insert_of_mem hx)
      exact h0 x₀ (Finset.mem_insert_self _ _)

/-- **Derivatives of families stay in a finite-dimensional space.** -/
theorem mem_of_hasDerivAt (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (F : ℝ → X → ℂ) (hF : ∀ t, F t ∈ V) (F' : X → ℂ)
    (hd : ∀ x, HasDerivAt (fun t => F t x) (F' x) 0) : F' ∈ V := by
  have hclosed : IsClosed (V : Set (X → ℂ)) := Submodule.closed_of_finiteDimensional V
  let s : ℝ → X → ℂ := fun t => ((t : ℂ)⁻¹) • (F t - F 0)
  have hs : ∀ t, s t ∈ V := fun t => V.smul_mem _ (V.sub_mem (hF t) (hF 0))
  have hlim : Filter.Tendsto s (𝓝[≠] (0 : ℝ)) (𝓝 F') := by
    refine tendsto_pi_nhds.2 fun x => ?_
    have h := (hasDerivAt_iff_tendsto_slope.1 (hd x))
    refine h.congr fun t => ?_
    simp [s, slope_def_module, sub_zero, Complex.real_smul]
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hs)

end Langlands.Archimedean.FiniteFunctionSpaces
