# Uniqueness of the actual common-Levi tensor germ

The primary construction is
`Langlands.Plancherel.ActualCommonLeviV3.regularGermValue`.
This module develops consequences of the published predicates in
`ActualCommonLeviV3Statement`. Its provenance is the actual tensor and
whole-operator regular-representative convention recorded there, specialized to
the common-Levi case of Waldspurger (2003), V.3 formula (1) and Lemma V.3.1
(printed p.295 / PDF p.61). The source is registered as
`waldspurger-2003-plancherel`. These are derived uniqueness facts, not a proof of
continuation existence, generic density or pole cancellation.

`polynomial_eq_zero_on_open_of_dense` tests a finite polynomial vector family
against each algebraic scalar linear functional. Each resulting scalar family
is an element of the evaluation-generated regular algebra, hence continuous.
Its zero values on the dense parameter set determine its values on the open
region. Algebraic dual separation recovers the vector identity, without a
topology or finite-dimensionality assumption on the vector space.

`IsLocalRepresentative.cross_eq` applies this result to the difference of the
cross-multiplied polynomial numerators of two local representatives. On the
generic locus both are the specified actual compact tensor, and scalar
commutativity makes their difference zero. `RegularGermAt.unique` evaluates the
identity at a point in both open sets and cancels both nonzero denominators.
Thus denominators need not agree.

`regularGermValue` extracts a compact operator from the supplied existence of a
regular value at an ambient point. Its specification is the existing
`RegularGermAt` predicate, and `regularGermValue_eq` proves independence from the
choice of representative when the genuine generic locus is ambiently dense.
Existence and density remain explicit hypotheses of these helpers.

`IsLocalRepresentative.generic_value` evaluates one representative at a point
of its genuine generic domain. `IsRegularUnitaryExtension.regularGermAt`
specializes the local extension identity to its center.
`IsRegularUnitaryExtension.isUniqueByRationalGerm` then obtains the published
uniqueness predicate from ambient generic density and regularity. All actual
field, cocharacter, compact subgroup and inducing data, including their
independent universes, are retained.

`IsRegularUnitaryExtension.agreesOnUnitaryGeneric` first evaluates a local
representative at a unitary generic point. It then uses the published
`compactComparison_square` and injectivity of `compactTensorEquiv` to recover
equality of the actual full product-action intertwiners. This agreement does
not require generic density. None of these lemmas supplies an extension or
asserts the coefficient or Hermitian identities of the closed target.
