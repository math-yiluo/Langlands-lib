# Fixed vectors of an ordered Coxeter product

Worker 1317. This is internal linear-algebra support for the split Steinberg
quotient proof, derived from Mathlib's root-pairing reflection and base definitions
and the Library's finite-coroot-index restriction-map theorem. It has no external
source claim.

For a finite independent family of vectors over a commutative ring, an ordered
product of linear automorphisms of the form `y ↦ y - l_j(y) • a_j` fixes a vector
exactly when every `l_j` vanishes on it. `orderedLinearOrbit` records the
successive suffix images. Their differences are scalar multiples of the
independent directions and telescope to zero when the path closes. Independence
forces every coefficient to vanish, so all suffix images coincide. The converse
follows by induction over the finite product. This is implemented in
`orderedReflection_fixed_iff` without assumptions on characteristic or on the
rank.

For a root pairing with a supplied base and ordering of its support,
`orderedCoxeter` is the actual ordered product of the simple reflections.
`orderedCoxeter_eq_self_iff` identifies its fixed vectors with the common
annihilator of the simple coroots. This assertion preserves central directions
for general reductive root pairings.

For an integer root datum with finitely many roots and finite quotient of the
coweight lattice by the coroot span, `orderedCoxeter_eq_self_iff_eq_zero` proves
that zero is the only fixed vector. Indeed, the base coroots span the entire
coroot lattice, so the annihilator condition kills the restriction of a character
to that lattice. The imported
`SimplyConnectedRootDatum.injective_toRootDatum_weightMap` makes this restriction
injective under the finite-index hypothesis, forcing the character to be zero.
The converse is linearity. No integral coroot-generation assumption is used.

These are abstract linear and lattice results. The file does not construct a
torus map, a cyclic representative gauge, fundamental characters, or the
canonical quotient isomorphism.
