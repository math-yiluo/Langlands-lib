# Generalized Whittaker coefficient distributions

Author: Worker 16.

This module constructs an actual bilinear map from two spaces of Whittaker
functionals to the algebraic distributions satisfying the published
bi-equivariance law. All new declarations are in `Langlands.Whittaker`.

## Distributions and characters

For a commutative topological ring `F`, a bundled
`UnitaryAdditiveCharacter F` named `ψ`, and `n : ℕ`,
`biEquivariantDistributions ψ n` is a complex submodule of
`HarmonicAnalysis.Distribution (GeneralLinear (n + 1) F)`. A distribution
here is a complex-linear functional on the actual locally constant compactly
supported complex functions; no topology on its dual is imposed.
The submodule consists exactly of distributions `D` such that

```text
D (g ↦ f(u₁ * g * u₂)) = χψ(u₁) * χψ(u₂) * D(f)
```

for every pair of elements of the actual upper-unipotent subgroup and every
test function `f`. Here `χψ = standardCharacter ψ n`. This is precisely
`IsBiEquivariantDistribution ψ n D`, with no changed signs or additional
condition. `mem_biEquivariantDistributions` exposes that membership equivalence.
Closure under zero, sums and complex scalar multiples follows pointwise.

For a topological field `F`, the published
`Langlands.RankinSelberg.standardCharacter_scale_neg_one` identifies
`standardCharacter (ψ.scale (-1)) n` with `inverseStandardCharacter ψ n`.
The scale uses the unit `-1 : Fˣ`, so the scaled additive character sends
`x` to `ψ(-x)`. The proof reuses `scaledStandardCharacter_neg_one` through
the definition of character transport. No characteristic restriction is needed.

## Coefficient construction

The field `F : Type uF` and representation carrier `V : Type uV` have
independent universe parameters. The coefficient construction assumes:

* `F` is a field with a topology making it a topological ring;
* `G = GeneralLinear (n + 1) F` is Hausdorff, locally compact and totally
  disconnected, with a measurable structure satisfying `BorelSpace`;
* `V` is an additive commutative group and complex module;
* `μ` is a measure on `G`, finite on compact sets and invariant under both
  left and right multiplication;
* `ρ : Representation ℂ G V` is smooth, with supplied proof `hρ`.

In particular, neither a unitary structure on `V` nor admissibility,
irreducibility, second countability, inversion invariance of `μ`, or a
nonzero functional is assumed.

`glCoefficientDistribution ψ n μ ρ hρ` is the complex-linear map

```text
glFunctionals ψ n ρ →ₗ[ℂ]
  glInverseFunctionals ψ n (smoothContragredient ρ) →ₗ[ℂ]
    biEquivariantDistributions (ψ.scale (-1)) n.
```

Both input spaces are the existing submodules of full algebraic duals.
The second is a submodule of the algebraic dual of the actual smooth dual
`SmoothDual ρ`; it does not require that its member `η` be smooth.
For inputs `ℓ` and `η`, the underlying distribution is exactly
`generalizedCoefficient μ ρ hρ ℓ.val η.val`. Its evaluation is

```text
Dℓ,η(f) = η(Sℓ(f)),       Sℓ(f)(v) = ℓ(ρ(f)v),
```

where `ρ(f)` is the existing integrated Hecke action for `μ`. These are
complex-bilinear expressions, with no complex conjugation.
`glCoefficientDistribution_val` and `glCoefficientDistribution_apply`
give the underlying-distribution and evaluation equalities, respectively.

The covariance theorem `generalizedCoefficient_isBiEquivariant` proves that
this distribution lies in the stated codomain. The input laws are
`ℓ(ρ(u)v) = χψ(u) ℓ(v)` and
`η(ρ∨(u)λ) = χψ(u)⁻¹ η(λ)`, with `ρ∨ = smoothContragredient ρ`.
The existing `generalizedCoefficient_biTranslate` evaluates the first law
at `u₁⁻¹` and the second at `u₂`. Therefore

```text
Dℓ,η(g ↦ f(u₁ * g * u₂)) =
  χψ(u₁)⁻¹ * χψ(u₂)⁻¹ * Dℓ,η(f).
```

The character identity above makes this precisely bi-equivariance for
`ψ.scale (-1)`. The implementation first precomposes the published
bilinear coefficient map with the inverse-functional submodule inclusion,
then restricts its codomain using the covariance theorem. Linearity in
the first input follows from the original coefficient map's linearity.
Rank one (`n = 0`) is included.

## Provenance and scope

This is an internal construction from the published actual objects in
`Whittaker.Distribution`, `Whittaker.GeneralizedCoefficient`,
`Whittaker.GeneralLinear`, and `HarmonicAnalysis.CharacterTransport`, together
with the character identity in `RankinSelberg.FunctionalEquationStatement`.
The provenance is restriction of a bilinear map to two existing subspaces,
with codomain membership deduced from its existing translation identity.
It is not a transcription of a separate literature theorem.

The module constructs coefficients for supplied functionals. It neither
constructs a nonzero `η` nor asserts Weyl-transpose invariance, the
generalized-coefficient kernel criterion, or Whittaker multiplicity one.
Those remain separate proof obligations.
