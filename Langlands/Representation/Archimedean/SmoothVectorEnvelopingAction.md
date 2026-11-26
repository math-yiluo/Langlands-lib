# The enveloping algebra acting on smooth vectors

Module `Langlands.Representation.Archimedean.SmoothVectorEnvelopingAction`, namespace
`Langlands.Archimedean.SmoothVectorEnveloping`.

## Setting

`M` is a real Lie group modelled on a real normed space `A` (`ChartedSpace A M`,
`LieGroup 𝓘(ℝ, A) ∞ M`), `E` a complex inner product space and `π : M →* (E →L[ℂ] E)`. Smooth
vectors and the derivatives `dπ(X) v = lieDerivative 𝓘(ℝ, A) π X v` are those of
`Langlands.Representation.Archimedean.SmoothVectors`. From `smoothLieAction` on, `A` is complete,
`M` also carries `LieGroup 𝓘(ℝ, A) (minSmoothness ℝ 3) M` (for the bracket of
`GroupLieAlgebra 𝓘(ℝ, A) M`), and `hcalc : smoothVectorFieldCommutator 𝓘(ℝ, A) M` is the scalar
commutator law for vector fields of `Langlands.Geometry.Manifold.VectorFieldCommutatorStatement`.
`𝔘` is `UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, A) M)`.

## Matrix coefficients

- `hilbertCoefficient π u w` is `g ↦ ⟪u, π g w⟫`; `contMDiff_hilbertCoefficient`: it is smooth
  for a smooth `w`.
- `mfderiv_clm_orbit`: for a continuous real-linear `ℓ : E → ℂ` and a smooth `w`, the derivative
  at `1` of `h ↦ ℓ (π (g h) w)` in the direction `X` is `ℓ (π g (dπ(X) w))` (chain rule for
  `ℓ ∘ π g ∘ orbitMap π w`).
- `groupDirectionalValue_hilbertCoefficient` (and its function form `_fun`): the right
  differentiation `groupDirectionalValue X` of `Langlands.Geometry.Manifold.SmoothGroupDifferential`
  maps the coefficient of `w` to the coefficient of `dπ(X) w`.
- `eq_of_hilbertCoefficient_one`: vectors with equal coefficients at `1` for every `u` are equal.

## Laws of `dπ`

- `lieDerivative_lie`: `dπ([X, Y]) w = dπ(X) dπ(Y) w - dπ(Y) dπ(X) w` for smooth `w`. The proof
  evaluates coefficients at `1` and uses `groupDirectionalValue_commutator_of_vectorFieldCommutator`
  for the smooth function `hilbertCoefficient π u w`.
- `apply_lieDerivative_eq`: `π g (dπ(X) w) = dπ(Ad(g) X) (π g w)` with
  `Ad(g) = groupTangentConjugation 𝓘(ℝ, A) g`, from `groupDirectionalValue_rightTranslation` applied
  to `hilbertCoefficient π u w`, whose right translate by `g` is `hilbertCoefficient π u (π g w)`.

## The enveloping action

- `Langlands.Archimedean.InfinitesimalCharacter.envInduction`: induction over `UniversalEnvelopingAlgebra ℂ L` (scalars, generators,
  products, sums), through the surjection from the tensor algebra.
- `generatorInduction`: induction over the generators `ι Z`, `Z ∈ ℂ ⊗[ℝ] L`.
- `smoothLieAction π hcalc : GroupLieAlgebra 𝓘(ℝ, A) M →ₗ⁅ℝ⁆ Module.End ℂ (smoothVectors 𝓘(ℝ, A) π)`
  sends `X` to `smoothLieDerivative 𝓘(ℝ, A) π X`; additivity and real homogeneity in `X` are those
  of `mfderiv`, and the bracket law is `lieDerivative_lie`.
- `envelopingAction π hcalc : 𝔘 →ₐ[ℂ] Module.End ℂ (smoothVectors 𝓘(ℝ, A) π)` is
  `Langlands.Algebra.ComplexLieExtension.enveloping (smoothLieAction π hcalc)`;
  `envelopingAction_ι_tmul` (`ι (c ⊗ X)` acts by `c • dπ(X)`) and `envelopingAction_algebraMap`.
- `apply_envelopingAction`: for an algebra endomorphism `φ` of `𝔘` with
  `φ (ι (c ⊗ X)) = ι (c ⊗ Ad(g) X)`, `π g (dπ(y) v) = dπ(φ y) (π g v)` for every `y`; induction
  over `y` with `apply_lieDerivative_eq` on generators.
- `exists_formalAdjoint`: if `π` is unitary, every `y` has some `y'` with
  `⟪dπ(y) v, w⟫ = ⟪v, dπ(y') w⟫` for smooth `v, w`. On generators `y' = ι (-c̄ ⊗ X)` by the skew
  symmetry `SmoothFunctionalOrbit.inner_lieDerivative_eq_neg`; products reverse order.

## Commuting operators and coefficients

- For a bounded `σ` commuting with every `π g`: `isSmoothVector_comm` (σ preserves smooth vectors),
  `lieDerivative_comm` (`dπ(X) (σ v) = σ (dπ(X) v)`), `smoothCommuting` (the restriction of `σ`)
  and `envelopingAction_comm` (`σ (dπ(y) v) = dπ(y) (σ v)`).
- `envelopingAction_coefficient`: let `Θ : 𝔘 →ₐ[ℂ] Module.End ℂ S` act on a space `S` of
  functions on `M` with `ι (1 ⊗ X)` acting by `groupDirectionalValue X`, let `W` be a space of
  smooth vectors stable under every `dπ(X)`, and `ℓ` a linear form whose coefficients
  `g ↦ ℓ (π g w)`, `w ∈ W`, lie in `S` and satisfy
  `groupDirectionalValue X (g ↦ ℓ (π g w)) = (g ↦ ℓ (π g (dπ(X) w)))`. Then for every `y`,
  `dπ(y)` preserves `W` and `Θ y` maps the coefficient of `w` to the coefficient of `dπ(y) w`.
  Induction over `y`; a generator `ι (c ⊗ X)` is `c • ι (1 ⊗ X)`.

## Provenance

Internal. The construction is the standard derived action of the enveloping algebra on smooth
vectors. Its Lie law is not proved directly on vectors: it is transported from the Lie law of the
right differentiations of smooth functions through the Hilbert matrix coefficients, which separate
vectors.
