# Finite cup reciprocity and transfer over an arbitrary intermediate field

This internal construction uses the published relative Tate restriction,
degree-minus-two abelianization comparison and degree-zero unit-class
comparison. The middle field is not required to be normal over the base.

`relativeAbelianizationTransfer` is Mathlib's finite-coset transfer to the
subgroup of automorphisms over the middle field, followed by the actual
scalar-restriction group equivalence. The single-chain comparison proves
that integral Tate restriction in degree minus two is this transfer.

In degree zero, subgroup reindexing and the existing restriction formula
send the class of a base-field unit to the class of its actual field
inclusion. Scalar-tower compatibility identifies the embedded coefficients.
These are derived comparisons, not new class field theory assumptions.

When the top field is finite Galois over the base and the middle field,
the degree-zero comparison identifies the two groups with the existing
field norm quotients. Restriction preserves zero, so a base-field norm
remains a norm after inclusion in the middle field.
`normQuotientTowerInclusion` is consequently the quotient map of the
literal field inclusion. Its value on every unit class is proved explicitly.

The published cup restriction theorem applies to an arbitrary relative
degree-two class and its restriction. In degree minus two, the two
comparisons above turn that theorem into the finite group-transfer and
field-inclusion square for `abelianizationCupToNormQuotient`.
If the two cup maps are bijective, injectivity of the corresponding cup
equivalence proves the reverse square for `arithmeticReciprocityOfCup`.
Output inversion gives the square for `geometricReciprocityOfCup`.

The bijectivity certificates and the degree-two class are explicit
parameters. These results do not assert that the inverse-cup maps are the
published normalized finite Artin symbols, nor that a common-closure Weil
system exists. Those comparisons and the passage from finite transfer to
actual topological Weil transfer remain separate obligations.
