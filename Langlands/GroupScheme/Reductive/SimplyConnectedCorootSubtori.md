# Closed coordinate subtori from subsets of a simple-coroot basis

For a full coordinate root datum `P` whose integral coroot span is the whole
coweight lattice, this internal module constructs the closed split subtorus
specified by any subset of the simple coroots of a base. The construction works
over an arbitrary base scheme. It retains an actual retraction and an exact
pullback formula for every fixed-exponent character.

The full perfect pairing and the integral simple-coroot basis identify a
character with its pairings against all simple coroots. Restriction to the
chosen subset has an integral right inverse given by extension by zero.
`splitTorus.exponentHom` turns these lattice maps into actual torus maps. The
lattice right inverse becomes a retraction. The section is a closed immersion
because the retraction is separated, as the ambient torus is affine over its
base.

For a finite reduced datum, take the subset complementary to a Cartan
component. A root restricts to zero on this subtorus exactly when its component
is the chosen one. The proof uses the unique simple-coroot component support
from `SimplyConnectedCartanComponents`, symmetric vanishing of Cartan
pairings, and the fact that the full character coordinate map is injective.
This is an integral equality; no claim that characters over an empty scheme
detect integer exponents is made.

These are internally derived consequences of the Library's coordinate torus
maps and integral simple-coroot basis, with Mathlib's perfect-pairing dual
basis constructions. The motivating use is the complementary-torus recovery
of factors in Conrad, *Reductive group schemes* (2014), Proposition 6.4.4,
pp.232–233. No simple-factor or product-isomorphism assertion is made here.
