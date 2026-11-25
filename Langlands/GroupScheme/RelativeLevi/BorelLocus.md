# The Borel locus and its compatibility with base change

`RelativeLevi.borelLocus i` is the set of base points where the actual
residue-field homomorphism induced by `i` satisfies the published predicate
`IsGeometricBorelSubgroup`. This definition simply names the set in
`RelativeBorelLocusClopenStatement`; it makes no openness assertion.

The supporting modules `BorelFieldTransport` and `BorelFiberTransport` derive
compatibility with arbitrary base change for a relative parabolic in a
reductive group. Over fields, the geometric Borel property persists and is
reflected under arbitrary extensions. At field-valued points, factorization
through the image's residue field and the actual pullback comparison identify
the predicates. Applying this at every residue-field point proves
`borelLocus_baseChange`. The supporting modules' Markdown describes those
proofs and their precise hypotheses.

This is internal notation and a derived transport interface for the published
Borel-locus target, without a new literature assertion. This helper does not
prove that the locus is open or closed.
