# Descent of scalar-localization units through a closed-fibre restriction

This internal algebraic construction is intended for restriction between
affine opens that meet the closed fibre over a valuation ring. It does not
assume that a torsionfree module is projective.

First, for any local commutative ring `R` and any `R`-algebra `C` for which
the extended maximal ideal is proper,
`isUnit_of_algebraMap_isUnit_of_closedFibre_ne_top` reflects scalar units
from `C` to `R`. A nonunit scalar belongs to the maximal ideal, and its
image therefore cannot be a unit in a proper extended ideal.

Over any valuation domain, assume also that `C` is torsionfree as an
`R`-module. If `r` and `d` are nonzero base scalars and `c` and `e` are
units of `C`, `exists_baseUnit_of_smul_units_eq` proves that an equality
`r • c = d • e` implies `d = r * t` for a unit `t` of `R`. Total
divisibility compares the two scalars. Cancellation of the smaller scalar
makes their quotient a unit in `C`, and the preceding reflection result
makes it a unit in `R`. No projectivity or prime closed-fibre condition on
`C` is needed.

`scalarLocalization_injective_of_torsionFree` proves injectivity of
`C → D` when `D` localizes `C` at the images of the nonzero scalars of the
base domain. Equality after localization can be cleared by one such scalar,
which cancels by torsionfreeness. This result does not require a valuation
ring or a nonempty closed fibre.

For the descent construction, let `A` be a projective `R`-algebra with
prime extended maximal ideal, and let `B` be its scalar localization.
Let `D` be the scalar localization of the torsionfree algebra `C` above.
Supply an actual `R`-algebra map `f : A → C` and an actual ring map
`g : B → D` whose square with the two localization maps commutes.
For `b : Bˣ` and `c : Cˣ` with `g(b)` equal to the image of `c`,
`exists_unit_of_scalarLocalization_restriction` supplies a unit of `A`
whose image in `B` is exactly `b`.

The proof uses the imported projective scalar-times-unit decomposition
of `b`. Restricting its cleared equation and using injectivity of `C → D`
compares two scalar multiples of total units in `C`. The resulting base
unit converts the original decomposition into a total-unit lift of `b`;
the original denominator cancels because it is a localization unit.
`scalarLocalizationUnitOfRestriction` chooses this actual total unit and
stores the exact image equality in its subtype.

The independent universes of the base, both total algebras and both
localizations are retained. The hypotheses apply to valuation domains
of arbitrary rank, including fields. This is internal derived content
from the published projective decomposition and Mathlib's valuation,
ideal and localization interfaces. It supplies neither geometric
projectivity nor compatible generic frames or a global line bundle.
