import Langlands.Representation.Archimedean.SmoothInvariantSubspace
import Langlands.Representation.Archimedean.SmoothFunctionalOrbit

/-!
# Orbits of functionals continuous on the smooth vectors of a closed invariant subspace

Let `π` be a unitary representation of a real Lie group on a complex Hilbert space `E` and `F₀`
a closed `π`-invariant subspace. Let `ℓ` be a linear form on `E` which, on the smooth vectors
lying in `F₀`, is bounded by finitely many of the seminorms `v ↦ ‖dπ(X₁ ⋯ Xₖ) v‖`. For a smooth
vector `w ∈ F₀`, the coefficient `g ↦ ℓ (π g w)` is smooth, and its derivative along right
multiplication is the coefficient of `dπ(X) w`.

This is `smoothFunctionalOrbit` applied to the restriction of `π` to the closure of the smooth
vectors of `F₀`, on which the smooth vectors are dense by construction.
-/

noncomputable section

open scoped Manifold ContDiff InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Archimedean.ClosedSubspaceFunctionalOrbit

open Langlands.Archimedean.SmoothInvariantSubspace

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {M : Type*} [Group M] [TopologicalSpace M] [ChartedSpace A M] [LieGroup 𝓘(ℝ, A) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : M →* (E →L[ℂ] E))

/-- **Orbits of a functional bounded on the smooth vectors of a closed invariant subspace.** -/
theorem contMDiff_and_mfderiv (hunit : ∀ g u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ)
    (F₀ : Submodule ℂ E) (hF₀c : IsClosed (F₀ : Set E)) (hF₀ : ∀ g v, v ∈ F₀ → π g v ∈ F₀)
    (ℓ : E →ₗ[ℂ] ℂ) (S : Finset (List A)) (C : ℝ)
    (hℓ : ∀ v, IsSmoothVector 𝓘(ℝ, A) π v → v ∈ F₀ →
      ‖ℓ v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs v‖)
    {w : E} (hw : IsSmoothVector 𝓘(ℝ, A) π w) (hwF : w ∈ F₀) :
    ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ (fun g => ℓ (π g w)) ∧
      ∀ (g : M) (X : A), mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun h => ℓ (π (g * h) w)) 1 X =
        ℓ (π g (lieDerivative 𝓘(ℝ, A) π X w)) := by
  set W₀ : Submodule ℂ E := smoothVectors 𝓘(ℝ, A) π ⊓ F₀ with hW₀
  have hW₀inv : ∀ (g : M) (v : E), v ∈ W₀ → π g v ∈ W₀ := fun g v hv =>
    ⟨isSmoothVector_apply 𝓘(ℝ, A) π hv.1 g, hF₀ g v hv.2⟩
  set U := W₀.topologicalClosure with hUdef
  have hU : ∀ g v, v ∈ U → π g v ∈ U := by
    intro g v hv
    exact map_mem_closure (π g).continuous hv (fun x hx => hW₀inv g x hx)
  have : CompleteSpace U := W₀.isClosed_topologicalClosure.completeSpace_coe
  have hUF : ∀ v ∈ U, v ∈ F₀ := by
    intro v hv
    have hsub : (W₀ : Set E) ⊆ F₀ := fun x hx => hx.2
    exact (hF₀c.closure_subset_iff.mpr hsub) hv
  let π' := restriction π U hU
  have hunit' : ∀ g (u v : U), ⟪π' g u, π' g v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro g u v
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact hunit g u v
  have hdense : DenseRange ((↑) : smoothVectors 𝓘(ℝ, A) π' → U) := by
    rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
    intro x
    have hx : (x : E) ∈ closure (W₀ : Set E) := x.property
    apply closure_mono _ hx
    intro y hy
    refine ⟨⟨y, subset_closure hy⟩, ?_, rfl⟩
    exact ⟨⟨⟨y, subset_closure hy⟩, isSmoothVector_of_coe π U hU 𝓘(ℝ, A) hy.1⟩, rfl⟩
  let L : smoothVectors 𝓘(ℝ, A) π' →ₗ[ℂ] ℂ :=
    ℓ ∘ₗ U.subtype ∘ₗ (smoothVectors 𝓘(ℝ, A) π').subtype
  have hL : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π' L := by
    refine ⟨S, C, fun v => ?_⟩
    have hv : IsSmoothVector 𝓘(ℝ, A) π ((v : U) : E) := isSmoothVector_coe π U hU 𝓘(ℝ, A) v.2
    have h := hℓ _ hv (hUF _ (v : U).2)
    have hsum : ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π' Xs v‖ =
        ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs ((v : U) : E)‖ := by
      refine Finset.sum_congr rfl (fun Xs _ => ?_)
      have he := iteratedLieDerivative_coe π U hU 𝓘(ℝ, A) Xs v
      rw [smoothInclusion_apply] at he
      rw [he]
      rfl
    rw [hsum]
    exact h
  let v' : smoothVectors 𝓘(ℝ, A) π' :=
    ⟨⟨w, subset_closure ⟨hw, hwF⟩⟩, isSmoothVector_of_coe π U hU 𝓘(ℝ, A) hw⟩
  obtain ⟨hsm, hder⟩ := smoothFunctionalOrbit A M U π' hunit' hdense L hL v'
  refine ⟨hsm, fun g X => ?_⟩
  have h := hder g X
  have hc := lieDerivative_coe π U hU 𝓘(ℝ, A) X v'.property
  change mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun h => ℓ (π (g * h) w)) 1 X =
    ℓ (π g ((lieDerivative 𝓘(ℝ, A) π' X (v' : U) : U) : E)) at h
  rw [h, ← hc]

end Langlands.Archimedean.ClosedSubspaceFunctionalOrbit
