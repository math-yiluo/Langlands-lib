# Etale shrinking of the actual nilradical model

This is a derived construction for the monic-model and shrinking step in
Stacks Project, Lemma 37.24.8 (0551), registered source
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`, proof.
It uses the actual lifted model of `FiniteSeparableNilradicalModel` and
constructs its finite free etale base change on a nonempty principal open
of the original base. The implemented generic etaleness proof uses the
derivative of a separable minimal polynomial rather than the source's
local-ring etaleness criterion.

The base is any commutative ring `R` with irreducible prime spectrum; it
may be nonreduced and is not assumed Noetherian. `K` is a specified
fraction field of the actual quotient `R / nilradical R`, and `L` is a
compatible specified finite separable extension of `K`. The quotient,
fraction-field and extension actions and their scalar towers are the
original supplied ones. `R`, `K`, and `L` have independent universes.

## Generic etaleness and shrinking

`etale_away_adjoinRoot_derivative` proves that a monic quotient becomes
etale after inverting its derivative: the standard etale presentation is
the polynomial together with its derivative and the tautological Bezout
identity. The comparison is Mathlib's actual localization equivalence.

For an actual `FiniteSeparableNilradicalModel d`,
`derivative_notMem_genericPrime` maps the derivative of the lifted
polynomial into `L`. The coefficient and root formulas and compatibility
of polynomial differentiation identify its value with the nonzero
derivative of the separable minimal polynomial. The proved equality of
the generic map with reduction followed by inclusion shows that this
derivative avoids the specified generic prime.
`isEtaleAt_genericPrime` follows from the basic-open criterion for the
etale locus.

`exists_etale_away_base` removes the closed image of the complement of
the etale locus under the finite map of prime spectra. The previously
proved uniqueness of the prime above the base nilradical shows that this
closed image misses the base generic point. A basic open neighborhood
then supplies `r` outside `nilradical R` such that localization at the
image of `r` is etale over `R`. No reduction of the original base is
performed in this shrinking argument.

`AwayCarrier d r` is the literal tensor product
`Localization.Away r` tensor over `R` with the lifted polynomial quotient.
It inherits finiteness and freeness by scalar extension.
`exists_etale_away` transports the etaleness through Mathlib's localization
and tensor-product comparison and descends scalars from `R` to the
principal localization. It proves etaleness over the actual localized base.

## The constructed model and its generic algebra

`FiniteSeparableNilradicalEtaleModel` stores the actual lifted model, the
denominator avoiding the base nilradical, and the proved etaleness of
its actual scalar extension. `finiteSeparableNilradicalEtaleModel`
constructs all these data using the preceding existence proof; etaleness
is not an unproved premise of this constructor.

For this constructed model `d`, `Base d` is the literal principal
localization of `R`, and `Carrier d` is the literal tensor product above.
The `finite`, `free`, and `isEtale` instances are proved for these objects.
`denominator_map_ne_zero` proves that the chosen denominator has nonzero
image in the original `K`. `baseToFractionField` is the localization lift
of the supplied map `R` to `K`, and `fractionAlgebra` and `fractionTower`
record this map and its compatibility with the original base action.

`genericEquiv` identifies `K` tensor over `Base d` with `Carrier d` with
the originally specified `L` as a `K`-algebra. Its proof cancels the actual
base change and uses the lifted polynomial model's proved generic
comparison. `genericEquiv_tmul` computes this comparison on an elementary
tensor: `k` tensor `(s` tensor `a)` maps to the image in `L` of
`(algebraMap (Base d) K s) * k`, multiplied by the original lifted
model's generic map of `a`. This preserves the specified scalar action.

This unit does not yet construct the scheme cover, its surjectivity,
or the comparison with the actual generic residue field and its scheme
triangle. Geometric-component splitting and full Stacks 0551 remain
separate obligations.
