# The actual shifted highest-product comparison

Author: Worker 103.

`Derivative.HighestProduct.shiftedHighestProductIso T ψ A B r s hr hs hA hB hrs`
constructs an actual smooth isomorphism

`ν^(1/2) (A × B)^(r+s) ≅ ν^(1/2) A^(r) × ν^(1/2) B^(s)`,

with the explicit ambient-rank transport from `(a-r)+(b-s)` to
`(a+b)-(r+s)`. Here all derivatives are the published actual determinant-normalized
Bernstein–Zelevinsky functors and each `ν^(1/2)` is the literal
`T.segmentFactor` at real exponent `1/2`.

The hypotheses are feasible orders `r ≤ a`, `s ≤ b`, `r+s ≤ a+b`, and vanishing
of all feasible derivatives of each factor above its supplied bound. The
factor ranks and orders may be zero. Neither nonvanishing at the bounds nor
irreducibility, finite length or unitarity is assumed. Thus the construction
also applies when the surviving derivatives are zero; it does not by itself
assert that the supplied sum is a highest nonzero order.

The factors have carrier universe `uV` and the binary output has carrier
universe `max uF uV`, with independent field and carrier universes.
The field's supplied topology and the supplied additive character `ψ` are
retained.

The proof twists the published `HighestProduct.highestProductIso` by
`|det|^(1/2)`, commutes this twist with equality transport of the ambient rank,
and applies `T.binaryNormalizedProductRealTwistIso` to the two factor
derivatives. The rank-transport comparison is identity after eliminating the
rank equality. The paired helper module `Induction.BinaryRealTwist` supplies
the common-twist comparison in all ranks, including the explicit zero-rank
tensor models.

The provenance is an internal composition of the published single-surviving-grade
highest-product construction and common determinant-character twisting.
This module supplies the structural comparison needed in the rank induction
for Bernstein's unitary product theorem; it does not assume or prove its
analytic positivity or irreducibility criteria.
