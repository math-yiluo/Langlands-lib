# Algebra laws of the actual rational Rosati operation

`Langlands.AbelianScheme.Rosati.algebraLaws` proves exactly the existing
`Langlands.AbelianScheme.Rosati.AlgebraLawsStatement` in every universe `u`.
The actual construction prerequisites, geometric polarization predicate, and
quantified rational inverse instance are retained unchanged.

The source is J. S. Milne, *Abelian Varieties*, January 2, 2022 author revision,
§17 p.35, registered as `milne-abelian-varieties-1986-author-2022`.
The original page, including its displayed formulas, and the full registered
errata snapshot `milne-abelian-varieties-1986-errata-2026-10-25` were read.
The errata says all its corrections are incorporated in this author revision.

Additivity and rational linearity use the existing bundled linear map.
The two `DualData` helper lemmas specialize the published identity and reversed
composition laws for the actual rational dual. Associativity of rational
composition and the actual inverse equations then give `involution_mul` and
`involution_id`. Rational linearity and the identity equation give
`involution_algebraMap`.

For `involution_involutive`, the proof uses the actual prime Weil pairing at
prime 2 over the identity geometric point. Its alternation follows from
`relativeFiniteWeilAlternation` and scalar extension; its nondegeneracy follows
from `primeRationalPolarizationWeilNondegeneracy`. The existing actual
`primeWeil_involution` adjunction, applied to both an endomorphism and its
Rosati conjugate, shows that the double conjugate and the original
endomorphism have the same pairing against every vector. Alternation reverses
the two arguments, and nondegeneracy makes their Tate operators equal.
The published `fieldPrimeRationalFaithfulness` then identifies the actual
rational endomorphisms. Characteristic zero ensures that prime 2 is invertible
in the base field.

This follows Milne's Weil-pairing route. It adds no biduality, dual involution,
trace comparison, finite-dimensionality, positivity, or rational inverse
existence premise.
