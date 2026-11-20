# Meromorphic functions with values in a finite-dimensional space of functions

Module `Langlands.Analysis.Meromorphic.FiniteDimensionalValues`, written by Worker 979 for
Task 5501 (`c1648848-1e63-45a5-8590-3e61a11b64f1`). It proves general lemmas about the
holomorphy and meromorphy predicates of `Langlands.Analysis.Meromorphic.AnalyticSystems` and
`Langlands.Analysis.Meromorphic.LinearCoordinates`. These predicates follow
Bernstein–Lapid §3.1 (registered source
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). The module adds no definitions and
no statements. All declarations are in the namespace `Langlands.Analysis.Meromorphic`.

Recall the predicates from those modules. `IsHolomorphicOn I f U` says that `s ↦ μ (f s)` is
complex differentiable on `U` for every continuous linear form `μ`. `IsMeromorphicOn I f U` says
four things: `U` is open and dense; `f` is holomorphic on `U`; and every point `s₀` has an open
connected neighbourhood `W`, a scalar `g` holomorphic on `W` and not identically zero on `W`, and
an `h` holomorphic on `W`, with `g s • f s = h s` for `s ∈ U ∩ W`.
`IsMeromorphicInCoordinatesOn f U` says that the source is finite-dimensional and that `f ∘ e`
is meromorphic with domain `e ⁻¹' U` for every linear isomorphism `e : ℂⁿ ≃ X`.

## Images under continuous linear maps

Let `L : V →L[ℂ] W` be a continuous linear map between complex topological vector spaces.

- `IsHolomorphicOn.continuousLinearMap_comp`: if `f` is holomorphic on `U`, so is
  `s ↦ L (f s)`. Proof: for a continuous linear form `μ` on `W`, `μ ∘ L` is a continuous linear
  form on `V`.
- `IsMeromorphicOn.continuousLinearMap_comp`: if `f` is meromorphic on `M` with domain of
  holomorphy `U`, so is `s ↦ L (f s)`, with the same `U`. Proof: keep the neighbourhood `W` and
  the denominator `g` for each point, and replace the numerator `h` by `L ∘ h`. Then
  `g s • L (f s) = L (g s • f s) = L (h s)`.
- `IsMeromorphicInCoordinatesOn.continuousLinearMap_comp`: the same for meromorphy in linear
  coordinates, chart by chart.

## Point evaluations and finite expansions

For a type `X`, the space `X → ℂ` carries Mathlib's product topology, the topology of pointwise
convergence.

`exists_continuousLinearMap_leftInverse`: let `b : ι → X → ℂ` be linearly independent, with `ι`
finite. Then there is a continuous linear map `Φ : (X → ℂ) →L[ℂ] (ι → ℂ)` with
`Φ (∑ i, c i • b i) = c` for all `c`. In words: the coordinates in the basis `b` of its span
extend to continuous linear functionals on all functions. The proof has four steps.

1. Let `T c = ∑ i, c i • b i`. It is injective because `b` is linearly independent. Let
   `L x : (ι → ℂ) → ℂ` be the functional `c ↦ (T c) x` for each `x ∈ X`.
2. The span of the `L x` in the dual of `ι → ℂ` is everything. Its dual coannihilator
   (`c` with `L x c = 0` for all `x`) is `{c | T c = 0} = 0`. In finite dimension a subspace of the
   dual is the annihilator of its coannihilator
   (`Subspace.dualCoannihilator_dualAnnihilator_eq`).
3. A linearly independent subfamily `L ∘ a` with the same span (`exists_linearIndependent'`) is
   finite, because the dual space is finite-dimensional. So `c ↦ (T c (a k))_k` is injective. It
   therefore has a linear left inverse `ψ` (`LinearMap.exists_leftInverse_of_injective`).
4. `Φ = ψ ∘ (restriction to the points a k)`. The restriction is continuous for the product
   topology. `ψ` is continuous, being linear on a finite-dimensional space.

`exists_meromorphic_expansion_of_mem_span`: take `E : Λ → (X → ℂ)` meromorphic in linear
coordinates with domain of holomorphy `D`, for the product topology. Take functions
`ψ : Fin k → X → ℂ`, all with some property `Pr`, and a set `S ⊆ Λ` such that `E λ` lies in the
span of the `ψ i` for `λ ∈ S`. Then there are `m`, `ψ' : Fin m → X → ℂ` and
`coeff : Fin m → Λ → ℂ` with three properties:

- every `ψ' i` is one of the `ψ j`, so `Pr (ψ' i)` holds;
- every `coeff i` is meromorphic in linear coordinates with the same domain of holomorphy `D`;
- `E λ x = ∑ i, coeff i λ * ψ' i x` for `λ ∈ S` and all `x`.

Proof. Let `ψ'` be a linearly independent subfamily of `ψ` with the same span
(`exists_linearIndependent'`), reindexed by `Fin m`. Take `Φ` from the previous lemma for `ψ'`,
and put `coeff i λ = Φ (E λ) i`. This is the image of `E` under the continuous linear map
`proj i ∘ Φ`, so it is meromorphic with domain `D` by the image lemma. For `λ ∈ S` write
`E λ = ∑ i, c i • ψ' i`. Then `Φ (E λ) = c`, which gives the expansion.

This is the elementary fact recalled in the Markdown of
`Langlands.Global.AdelicIntertwiningContinuationStatement`: a function with values in a
finite-dimensional space `W` is meromorphic exactly when its coefficients in a basis of `W` are.
Only the direction used later is proved, in the following form. The ambient topology is that of
pointwise convergence. The coefficients are given by finitely many point evaluations. These
evaluations extend continuously to all functions, so no topology on `W` beyond the product
topology is needed.

## Scope

No identity theorem in several complex variables is used, and none is proved. The coefficients
inherit the domain of holomorphy and the local denominators of `E` itself.
