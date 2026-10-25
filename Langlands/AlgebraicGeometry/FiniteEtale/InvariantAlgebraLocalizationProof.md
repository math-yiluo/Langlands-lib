# Fixed numerators after localization

This module proves
`Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraLocalization` from the
published `InvariantAlgebraStatements` module. The proof retains all its ring,
algebra-tower, finite-group-action, scalar-compatibility and equivariance
parameters, in the original universe.

The original source is Grothendieck et al., *SGA 1*, recomposed edition,
arXiv `math/0206203v2`, registered as `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
Exposé V, Corollary 1.2, printed p.88 / PDF p.104, uses the formula that
invariants commute with localization at a multiplicative subset of the
invariant ring. The published target is the internal elementwise
denominator-clearing consequence for powers of the base-ring element `r`.
The proof below supplies that consequence directly rather than constructing
the full localization isomorphism.

The private helper chooses one exponent for each member of a finite family of
equalities after multiplication by powers of a common element. Their finite
maximum works for every member: multiply its equality by the remaining power.
This helper uses only a commutative monoid and a finite index type.

For a fixed `b : B`, Mathlib's `IsLocalization.Away.surj` supplies a numerator
`a : A` and an exponent `n` such that the image of `a` is `r^n * b`, with all
base images interpreted through the given algebra tower. The `G`-action fixes
base scalars. Equivariance and the invariance of `b` therefore show that `g • a`
and `a` have the same image in `B` for every `g`. The localization equality
criterion clears each such equality by a power of the image of `r` in `A`.
The finite common-exponent helper supplies one exponent `m` for all `g`.
Multiplying `a` by that power gives a fixed element of `A`; its image is
`r^(m+n) * b`, as required.

The argument does not cancel elements of `A` or divide by the group order.
The base element may be a zero divisor, and the localization map need not be
injective. No noetherian, finite-module, étale, free-action, faithful-action or
invertible-order assumptions are added. The result asserts the exact published
elementwise numerator property.
