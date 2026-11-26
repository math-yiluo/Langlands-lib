import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Langlands.Analysis.OperatorIdeals
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Irreducible tempered components of a unitary representation

Let `π` be a unitary representation of a second countable locally compact group `G` on a complex
Hilbert space `H`, and `j : H → W` a bounded injective equivariant map into a Hilbert space `W`
with a continuous representation `π_W`, such that `j ∘ π(φ)` is Hilbert–Schmidt for every bounded
measurable compactly supported `φ`. The proposition `TemperedIrreducibleComponentStatement` asserts
that every nonzero closed invariant subspace `H₀` of `H` has an irreducible "tempered component":
a topologically irreducible unitary representation `σ` on a Hilbert space `V` with a nonzero
`G`-equivariant linear map `J` into `W`, defined on an invariant subspace `D` of `V` containing the
vectors `σ(φ) σ(ψ) u` (`ψ` in a prescribed countable family), bounded on each family
`u ↦ σ(φ) σ(ψ) u`, and with values in the closure of `j(H₀)`.

This is the single-fibre form of the Gelfand–Kostyuchenko method as Bernstein adapts it to
representation theory (J. Bernstein, *On the support of Plancherel measure*, 1988, §§1.2–1.5): in
a decomposition `H₁ = ∫ H_z dν(z)` of a cyclic subspace `H₁ ⊆ H₀` into irreducible representations
(G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., 2015, Theorems 7.29 and
7.30(b)), the Hilbert–Schmidt adjoints `(j π(φ)|_{H₁})^*`, restricted to the closure of `j(H₁)`,
are pointwise defined, and the adjoints of their fibre maps give, for almost every `z` with
`H_z ≠ 0`, the map `J` on the fibre `H_z`. -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Analysis

/-- Irreducible tempered components (Bernstein 1988, §§1.2–1.5, single-fibre form, with Folland
2015, Theorems 7.29 and 7.30(b)). Let `G` be a
second countable locally compact Hausdorff group with a left Haar measure `μ`, `π` a unitary,
jointly continuous representation of `G` on a complex Hilbert space `H`, and `H₀ ≠ 0` a closed
`π`-invariant subspace. Let `π_W` be a jointly continuous representation of `G` by bounded
operators on a complex Hilbert space `W`, and `j : H → W` a bounded injective linear map with
`j ∘ π(g) = π_W(g) ∘ j`, such that for every bounded measurable compactly supported
`φ : G → ℂ` the operator `x ↦ j(∫ φ(g) π(g) x dμ(g))` is Hilbert–Schmidt. Then for every countable
family `Φ` of bounded measurable compactly supported functions there are a complex Hilbert space
`V`, a unitary, jointly continuous, topologically irreducible representation `σ` of `G` on `V`, a
subspace `D` of `V` and a linear map `J : V → W` such that, writing
`σ(φ) u = ∫ φ(g) σ(g) u dμ(g)`:

* `D` is `σ(G)`-invariant and `J(σ(g) d) = π_W(g) (J d)` for `d ∈ D`;
* for every bounded measurable compactly supported `φ`: `D` is `σ(φ)`-invariant and
  `J(σ(φ) d) = ∫ φ(g) π_W(g) (J d) dμ(g)` for `d ∈ D`; and for every `ψ ∈ Φ`, the vectors
  `σ(φ) (σ(ψ) u)` lie in `D` and `‖J(σ(φ) (σ(ψ) u))‖ ≤ C ‖u‖` for a constant `C`;
* `J d ≠ 0` for some `d ∈ D`;
* `J d` lies in the closure of `j(H₀)` for every `d ∈ D`.

Only the restriction of `J` to `D` matters. -/
def TemperedIrreducibleComponentStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)),
    (∀ g, π g ∈ unitary (H →L[ℂ] H)) → Langlands.Archimedean.IsContinuousRepresentation π →
    ∀ H₀ : Submodule ℂ H, IsClosed (H₀ : Set H) → (∀ g, ∀ x ∈ H₀, π g x ∈ H₀) → H₀ ≠ ⊥ →
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
      (πW : G →* (W →L[ℂ] W)), Langlands.Archimedean.IsContinuousRepresentation πW →
    ∀ j : H →L[ℂ] W, Function.Injective j → (∀ g x, j (π g x) = πW g (j x)) →
    (∀ φ : G → ℂ, Measurable φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → HasCompactSupport φ →
      ∃ T : H →L[ℂ] W, (∀ x, T x = j (∫ g, φ g • π g x ∂μ)) ∧
        Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt T) →
    ∀ Φ : Set (G → ℂ), Φ.Countable →
      (∀ ψ ∈ Φ, Measurable ψ ∧ (∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C) ∧ HasCompactSupport ψ) →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
      (σ : G →* (V →L[ℂ] V)) (D : Submodule ℂ V) (J : V →ₗ[ℂ] W),
      (∀ g, σ g ∈ unitary (V →L[ℂ] V)) ∧
      Langlands.Archimedean.IsContinuousRepresentation σ ∧
      Langlands.Archimedean.IsTopologicallyIrreducible σ ∧
      (∀ g, ∀ d ∈ D, σ g d ∈ D ∧ J (σ g d) = πW g (J d)) ∧
      (∀ φ : G → ℂ, Measurable φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → HasCompactSupport φ →
        (∀ d ∈ D, (∫ g, φ g • σ g d ∂μ) ∈ D ∧
          J (∫ g, φ g • σ g d ∂μ) = ∫ g, φ g • πW g (J d) ∂μ) ∧
        ∀ ψ ∈ Φ, ∃ C : ℝ, ∀ u : V,
          (∫ g, φ g • σ g (∫ h, ψ h • σ h u ∂μ) ∂μ) ∈ D ∧
          ‖J (∫ g, φ g • σ g (∫ h, ψ h • σ h u ∂μ) ∂μ)‖ ≤ C * ‖u‖) ∧
      (∃ d ∈ D, J d ≠ 0) ∧
      ∀ d ∈ D, J d ∈ closure (j '' (H₀ : Set H))

end Langlands.Analysis
