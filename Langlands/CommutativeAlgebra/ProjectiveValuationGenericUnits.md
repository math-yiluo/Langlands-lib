# Primitive normalization and generic units for projective valuation algebras

This module extends the Library's free-module normalization and free-algebra
scalar saturation to projective modules and projective algebras over a
valuation domain. The domain has arbitrary rank, including rank zero, and
the base, algebra, and localization have independent universes.
No finite generation is required of a projective module.

The content is internally derived from
`FreeValuationAlgebraSaturation`, `FreeValuationGenericUnits`, and Mathlib's
definition of projectivity as a split embedding into a free module.
It does not invoke the separate, unproved
`IntegralFibreProjectivityStatement`, or assert that a smooth algebra is
projective.

For a nonzero element `x` of a projective module `M`,
`exists_scalar_normalization_of_projective` supplies a nonzero base scalar
`r`, an element `y` of `M`, and an `R`-linear functional `l : M → R` such
that `x = r • y` and `l y = 1`.
`scalarNormalizationOfProjective` chooses the corresponding
`ScalarNormalization` data. The theorem
`exists_scalar_normalization_not_mem_of_projective` forgets the functional
and retains that `y` lies outside the maximal-ideal multiple of `M`.

The implemented proof chooses a split embedding `s : M → M →₀ R` with
retraction `p`. The imported free-module result gives
`s x = r • z` and a functional `h` with `h z = 1`.
Applying `s ∘ p` to that equality and canceling the nonzero scalar in the
free module shows `s (p z) = z`. Thus `y = p z` and `l = h ∘ s` have the
required properties. Applying `l` to a hypothetical maximal-ideal
expression for `y` would put `1` in the maximal ideal.

For a projective commutative `R`-algebra `A`, the remaining results assume
that the ideal `mA`, the image of the base maximal ideal, is prime.
In particular, the closed fibre is nonempty and integral.
`scalar_dvd_iff_mul_dvd_of_projective_of_closedFibrePrime` states that,
if `s ∉ mA`, divisibility of `s * a` by any base scalar is equivalent to
divisibility of `a`. Normalize `a = d • a₀` with `a₀ ∉ mA`, then compare
`d` with the specified scalar using valuation divisibility. One direction
immediately gives the desired quotient; in the other, scalar cancellation
and primeness of `mA` force the comparison quotient to be a base unit.
Projectivity supplies flatness and hence the scalar cancellation used here.
This is the free-algebra proof with projective normalization in place of
free normalization.

`isUnit_of_dvd_scalar_of_projective_of_closedFibrePrime` applies that
saturation theorem to prove that a primitive divisor of a nonzero base
scalar is a unit. If `B` is any localization of `A` at the image of the
nonzero scalars of `R`, `scalarLocalization_injective_of_projective` proves
injectivity of `A → B` by scalar cancellation; that result does not need a
valuation or closed-fibre assumption.
`isUnit_scalarLocalization_iff_of_projective_of_closedFibrePrime` then
shows that a primitive element of `A` is a unit exactly when its image in
`B` is a unit.

Finally,
`exists_scalar_unit_decomposition_of_projective_of_closedFibrePrime`
states that every `b : Bˣ` admits nonzero `r d : R` and `a : Aˣ` satisfying

```
image(r) * b = image(d) * image(a).
```

The proof writes `b` as a localization fraction and normalizes its nonzero
numerator in the projective module `A`. The primitive normalized numerator
is a generic unit and therefore a total unit by the preceding theorem.
`scalarUnitDecompositionOfProjective` chooses the actual
`ScalarUnitDecomposition` data. No uniqueness, compatible choices on
overlaps, or global line-bundle extension is asserted.
