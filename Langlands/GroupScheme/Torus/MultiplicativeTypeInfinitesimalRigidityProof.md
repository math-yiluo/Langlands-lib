# Infinitesimal rigidity of homomorphisms from groups of multiplicative type

The theorem
`Langlands.GroupScheme.multiplicativeTypeInfinitesimalRigidity.{u}` proves
the proposition
`Langlands.GroupScheme.MultiplicativeTypeInfinitesimalRigidityStatement`
in every universe. The target group scheme is arbitrary.

The proof uses translation actions and fppf descent. It does not require the
smooth-target classification of lifts.

For a diagonalizable source D(M), translate the target G by the given
homomorphism. Triviality of the homomorphism after reduction modulo the
nilpotent base ideal makes this action trivial on every algebra annihilating
that ideal. Diagonalizable action rigidity then makes the action trivial on G
itself. Evaluating at the identity point recovers triviality of the
homomorphism.

The action-rigidity input is proved for arbitrary schemes. For an affine
scheme with coordinate algebra B, the natural character action gives
homogeneous linear projections on B. Each projection is idempotent.
Triviality modulo the nilpotent ideal makes the degree-zero projection
congruent to the identity and all other projections congruent to zero.
Rigidity of commuting idempotent endomorphisms modulo a nilpotent ideal
makes these equalities exact, so the action is trivial.

For a general scheme, residue-field tests show that the action and second
projection have the same underlying point map, since nilpotents vanish in
fields. Every open is therefore invariant. Restrict to each affine open,
apply the affine result, and glue the resulting morphism equalities on the
pullback of an affine open cover along the second projection.

Finally, a group of multiplicative type becomes diagonalizable on its
specified fppf cover. Refine that cover by affine open covers. On each affine
chart, map the nilpotent ideal to the chart ring; the resulting generated
ideal is still nilpotent. The induced map of quotient rings gives a
commutative square of spectra. Naturality of base-change comparison
isomorphisms transports reduced triviality to this chart. The diagonalizable
case makes the homomorphism trivial there. Equality of group-scheme
homomorphisms descends first along the affine open covers and then along
the fppf splitting cover.

The implemented argument has no affineness, smoothness, separatedness or
finite-presentation assumption on G, and no finite-generation assumption
on the character groups.
