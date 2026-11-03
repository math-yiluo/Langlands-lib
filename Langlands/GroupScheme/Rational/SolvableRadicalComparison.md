# Canonical comparison of represented solvable radicals

Author: Worker 1264.

This is an internal derived construction from the published
`IsSolvableRadical` predicate in `Rational.LeviSubgroup` and the represented
subgroup API. It proves no existence theorem for a radical, a rational Levi,
or a maximal split torus, and requires no structural theorem about parabolics.
The construction applies over every field in an arbitrary universe.

For two actual maps `r : R → P` and `r' : R' → P` satisfying
`IsSolvableRadical`, `range_eq` proves equality of their subgroup functors
on all relative test schemes. Each representative satisfies the closedness,
smoothness, connectedness, solvability and normality premises of the other
representative's greatestness field. Applying those fields gives the two
inclusions, and antisymmetry gives equality.

`iso` then uses closedness to obtain the monomorphisms and applies
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` to this equality.
Its homomorphism satisfies `iso_hom_comp`, the equality
`(hr.iso hr').hom ≫ r' = r` of actual group-scheme morphisms. The inverse
has the corresponding equality. `iso_hom_unique` cancels the closed
embedding `r'` to prove uniqueness among homomorphisms with this compatibility.
The word canonical means this precise uniqueness; it does not choose a
radical or identify the two representing objects by definitional equality.

For any `b : H → R`, `factor hr hr' b` is the composite of `b` with this
isomorphism. `factor_comp` proves that its composite with `r'` is exactly
`b ≫ r`, and `factor_unique` proves uniqueness. `factor_comp_ambient`
retains this equality after any further map `j : P → G`. Consequently any
property of that composite, including its whole-torus centralizer and
ambient maximal splitness when `H` is a torus, can be transported by
rewriting the equality. No rational-point comparison is used.

`isSplitSubtorus_factor` transports closedness by composition with the
comparison isomorphism. `isMaximalSplitTorus_factor` applies the published
descent of maximal splitness through a closed subgroup to the inverse
comparison isomorphism; the composite with that inverse is the original
subtorus. These conclusions concern maximality inside the radical.
They do not upgrade radical maximality to maximality in a larger group.

The geometric radical predicate implies the ground-field predicate used
here, so its representatives admit the same comparison by taking the first
conjunct. The algebraic-closure conjunct is unnecessary for these formal
laws. The provenance is the universal properties already present in the
imported definitions, rather than a new translation of a literature result.
