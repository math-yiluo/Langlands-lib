# Units in scalar localizations of free valuation algebras

Let `R` be a commutative valuation domain, let `A` be a commutative
`R`-algebra free as an `R`-module, and suppose that
`P = Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R)` is prime.
Let `B` be a commutative `A`-algebra localizing `A` at the image of the
nonzero base scalars, expressed by
`IsLocalization (Algebra.algebraMapSubmonoid A R⁰) B`.
The universes of `R`, `A` and `B` are independent. There is no restriction
on the rank of the valuation, and fields are included.

`isUnit_of_dvd_scalar_of_free_of_closedFibrePrime` proves that if `a ∉ P`
and `a` divides the image of a nonzero scalar `r : R`, then `a` is a unit.
Write `r = a * b` in `A`. The imported scalar saturation theorem shows
that `r` divides `b`, so `b = r * c`. Cancellation of the nonzero scalar
`r` in the free module gives `a * c = 1`.

`scalarLocalization_injective_of_free` proves that `algebraMap A B` is
injective. This auxiliary result only requires that `R` is a domain,
that `A` is free over `R`, and that `B` is the displayed scalar
localization; it does not require a valuation or prime closed-fibre ideal.
Equality in the localization is witnessed after multiplying by a scalar
in the denominator submonoid. That scalar comes from a nonzero element
of `R`, so torsion freeness cancels it.

`isUnit_scalarLocalization_iff_of_free_of_closedFibrePrime` proves

```text
IsUnit (algebraMap A B a) ↔ IsUnit a       if a ∉ P.
```

The localization unit criterion expresses `a` as a divisor of a nonzero
base scalar, and the preceding divisor result applies. The reverse
implication is preservation of units under a ring homomorphism.

`exists_scalar_unit_decomposition_of_free_of_closedFibrePrime` proves that
every `b : Bˣ` has nonzero scalars `r d : R` and an actual `a : Aˣ` with

```text
image(r) * b = image(d) * image(a)        in B.
```

Here a scalar's image is the composite `R → A → B`. Clear a denominator of
`b` to obtain a numerator in `A`. The prime ideal's properness and the
injective localization map give nontriviality, so this numerator is nonzero.
Normalize it as `d • a₀`, with `d ≠ 0` and `a₀ ∉ P`, using the imported free
module normalization. Its image is a unit, since a factor of a unit in a
commutative ring is a unit. Unit reflection then makes `a₀` an actual unit
of `A`, yielding the displayed equality.

`ScalarUnitDecomposition R A B b` stores these two nonzero scalars, the
actual total unit, and the equality after clearing the denominator. Its
data type only requires the displayed commutative rings and algebra
maps. `scalarUnitDecompositionOfFree` chooses these data by classical
choice from the proved existence result. No uniqueness or canonicity is
asserted.

This is an internal derivation from
`Langlands.CommutativeAlgebra.FreeValuationAlgebraSaturation` and Mathlib's
localization unit and denominator criteria. It makes no additional claim
from the original literature. Freeness of `A` and primality of its
closed-fibre ideal remain explicit: the file supplies neither a reduction
of a general smooth valuation algebra to this setting nor the geometric
unit lifts needed for the global two-axis line-bundle extension theorem.
