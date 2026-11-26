import Langlands.Representation.Archimedean.CompactSmoothFiniteDensity
import Langlands.Representation.Archimedean.SmoothFixedSubspace
import Langlands.Representation.Unitary.CompactIsometricAverage

/-!
# Compact-finite smooth vectors at a fixed level on which a functional does not vanish

Let `π` be a representation of a finite-dimensional real Lie group `M` on a complex Hilbert
space `E`, commuting with a second action `σ`, and let `L` be a subgroup for `σ`. Let a compact
group `K` map continuously to `M` and have a faithful continuous finite-dimensional
representation. If a linear form `ξ`, bounded on the smooth `L`-fixed vectors by finitely many
derivative seminorms, does not vanish at some smooth `L`-fixed vector, then it does not vanish at
some smooth `L`-fixed vector whose `K`-orbit spans a finite-dimensional space.

The proof restricts `π` to the closed subspace of `L`-fixed vectors, where `ξ` is continuous
for the derivative topology of the smooth vectors, and uses the density of the compact-finite
smooth vectors (`CompactSmoothFiniteDensity.dense_finiteSmoothVectors`).
-/

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Archimedean.FixedCompactFiniteChoice

open Langlands.Archimedean.SmoothInvariantSubspace

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {M : Type*} [Group M] [TopologicalSpace M] [ChartedSpace A M] [LieGroup 𝓘(ℝ, A) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {Φ : Type*} [Group Φ]
  (σ : Φ →* (E →L[ℂ] E)) (L : Subgroup Φ) (π : M →* (E →L[ℂ] E))
  (hcomm : ∀ g l v, π g (σ l v) = σ l (π g v))

include hcomm in
/-- **A compact-finite smooth fixed vector on which `ξ` does not vanish.** -/
theorem exists_compactFinite_ne_zero
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
    [CompactSpace K] (r : K →ₜ* M) {ι : Type*} [Fintype ι]
    (τ : Representation ℂ K (ι → ℂ)) (hτ : ∀ v, Continuous fun k => τ k v)
    (hinj : Function.Injective τ) (ξ : E →ₗ[ℂ] ℂ) (S : Finset (List A)) (C : ℝ)
    (hξ : ∀ v, IsSmoothVector 𝓘(ℝ, A) π v → v ∈ fixedSubspace σ L →
      ‖ξ v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs v‖)
    {v₀ : E} (hv₀ : IsSmoothVector 𝓘(ℝ, A) π v₀) (hv₀L : v₀ ∈ fixedSubspace σ L)
    (hξv₀ : ξ v₀ ≠ 0) :
    ∃ v : E, IsSmoothVector 𝓘(ℝ, A) π v ∧ v ∈ fixedSubspace σ L ∧ ξ v ≠ 0 ∧
      FiniteVectors.IsFiniteVector
        (CompactSmoothFiniteDensity.restrictedRepresentation π r) v := by
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let U := fixedSubspace σ L
  let πL := fixedRestriction σ L π hcomm
  have hU : ∀ g v, v ∈ U → π g v ∈ U := fun g v hv => fixedSubspace_invariant σ L π hcomm g v hv
  let μ : Measure K := Analysis.compactProbabilityHaar K
  have hd := CompactSmoothFiniteDensity.dense_finiteSmoothVectors (𝔤 := A) πL r μ τ hτ hinj
  -- the functional on the smooth vectors of the fixed level
  let ℓ : smoothVectors 𝓘(ℝ, A) πL →ₗ[ℂ] ℂ :=
    ξ ∘ₗ U.subtype ∘ₗ (smoothVectors 𝓘(ℝ, A) πL).subtype
  have hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) πL ℓ := by
    refine ⟨S, C, fun v => ?_⟩
    have hv : IsSmoothVector 𝓘(ℝ, A) π ((v : U) : E) := isSmoothVector_coe π U hU 𝓘(ℝ, A) v.2
    have h := hξ _ hv (v : U).2
    have hsum : ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) πL Xs v‖ =
        ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs ((v : U) : E)‖ := by
      refine Finset.sum_congr rfl (fun Xs _ => ?_)
      have he := iteratedLieDerivative_coe π U hU 𝓘(ℝ, A) Xs v
      calc ‖iteratedLieDerivative 𝓘(ℝ, A) πL Xs v‖ =
          ‖((iteratedLieDerivative 𝓘(ℝ, A) (restriction π U hU) Xs v : U) : E)‖ := rfl
        _ = _ := by rw [← he]; rfl
    rw [hsum]
    exact h
  have hcont := continuous_of_isContinuousOnSmoothVectors 𝓘(ℝ, A) πL ℓ hℓ
  let O : Set (DerivativeSmoothVectors 𝓘(ℝ, A) πL) :=
    {w | ℓ (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) πL w) ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hcont continuous_const
  let w₀ : smoothVectors 𝓘(ℝ, A) πL :=
    ⟨⟨v₀, hv₀L⟩, isSmoothVector_of_coe π U hU 𝓘(ℝ, A) hv₀⟩
  have hO₀ : ((DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) πL).symm w₀) ∈ O := by
    change ℓ ((DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) πL)
      ((DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) πL).symm w₀)) ≠ 0
    rw [LinearEquiv.apply_symm_apply]
    exact hξv₀
  obtain ⟨w, hwO, hwfin⟩ := hd.inter_open_nonempty O hO ⟨_, hO₀⟩
  let u : smoothVectors 𝓘(ℝ, A) πL := DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) πL w
  refine ⟨((u : U) : E), isSmoothVector_coe π U hU 𝓘(ℝ, A) u.2, (u : U).2, hwO, ?_⟩
  let jK : Representation.IntertwiningMap
      (CompactSmoothFiniteDensity.restrictedRepresentation πL r)
      (CompactSmoothFiniteDensity.restrictedRepresentation π r) :=
    { toLinearMap := U.subtype
      isIntertwining' := fun k => LinearMap.ext fun x => rfl }
  exact (show FiniteVectors.IsFiniteVector
    (CompactSmoothFiniteDensity.restrictedRepresentation πL r) (u : U) from hwfin).map jK

end Langlands.Archimedean.FixedCompactFiniteChoice
