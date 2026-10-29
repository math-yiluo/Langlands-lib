# Polynomial annihilation on the actual finite joint orbit

The theorem
`Langlands.Global.ArchimedeanGL.jointOrbitPolynomialAnnihilation` proves
`JointOrbitPolynomialAnnihilationStatement K n` for an arbitrary number
field in every universe and every natural rank, including zero. It imports the unchanged published statement from
`Langlands.Global.ArchimedeanJointPolynomialStatement`. Worker 94 supplied
the initial proof; Worker 88 inspected the imported constructions and
prepared this focused contribution.

The proof first treats an arbitrary complex vector space, an invariant
subspace `S`, and an ambient linear endomorphism `L`. The helper
`coe_aeval_restrict` identifies polynomial evaluation of the restricted
endomorphism with ambient polynomial evaluation after inclusion. Its
polynomial induction has an additive case and a monomial case; the latter
uses `Module.End.pow_restrict` and the linear inclusion's compatibility
with scalar multiplication.

The helper `polynomial_annihilator_of_invariant` assumes that `S` is
finite-dimensional and takes the characteristic polynomial of the
restriction of `L`. Mathlib supplies monicity, degree equal to
`Module.finrank ℂ S`, and the Cayley–Hamilton identity. Evaluating that
identity on each vector of `S`, including it into the ambient vector
space, and applying `coe_aeval_restrict` gives one polynomial annihilating
every vector in `S`.

For the actual smooth-function carrier,
`center_add_compact_preserves_jointOrbit` obtains invariance under a
central action and under a compact enveloping action from the published
`jointOrbitSubrepresentation`. Additivity of the genuine enveloping
action proves invariance under their sum. The main theorem uses the
generic finite-dimensional helper on this actual joint orbit. Finally,
`Polynomial.aeval_algHom_apply` for the actual `envelopingAction` turns
the endomorphism-polynomial identity into the specified enveloping
algebra polynomial identity. The existing `IsJointFinite` hypothesis
provides precisely the finiteness of this joint orbit, without any claim
about the dimension of the ambient smooth functions.

This is an internal linear algebra derivation from published joint-orbit
invariance and Mathlib's Cayley–Hamilton theorem; no external literature
result is invoked. The characteristic-polynomial argument has no positive-dimension premise.
For a zero joint orbit its characteristic polynomial is the monic
degree-zero polynomial, so the same argument includes the zero function.
Neither the construction nor the proof requires positive rank.

No analytic regularity, ellipticity, jet uniqueness, reproduction or final
automorphic growth is asserted.
