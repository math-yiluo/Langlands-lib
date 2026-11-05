# Trivial Weyl stabilizers of regular weights and coweights

This internal derived module concerns a finite crystallographic root pairing
over a linearly ordered field. It permits nonreduced pairings, roots that
do not span the weight space, independent universes and an empty root set.
It constructs no algebraic group, torus, actual normalizer representative,
or character associated with half the sum of positive roots.

The published `rootPairingWeylCoxeterStatement_proof` gives a Coxeter
system on the simple roots selected by a regular functional, together
with the root-sign length law. If a Weyl element preserves positivity
of every positive root, every simple right multiplication increases
length. A nonidentity element has a right descent, a contradiction.
Thus such a Weyl element is the identity. This proves triviality of the
stabilizer of a regular functional under pullback by the natural Weyl
action. Pairing compatibility gives the corresponding statement for a
coweight whose evaluation on every root is nonzero.

For weights, the module uses the canonical root form. Its value at a
root paired with itself is positive, because it is a sum of squares
including the square of two. Mathlib's canonical-form identity says that
twice the pairing with a root is this positive number times evaluation
by the corresponding coroot. Therefore a weight nonzero on every coroot
defines a regular functional through the root form. Weyl invariance of
that form makes a Weyl element fixing the weight fix this functional,
so it is the identity.

The definition `regularWeightOrbitEquiv` sends each Weyl element to its
action on the supplied coroot-regular weight. If two elements give the
same weight, their ratio fixes it and the proved stabilizer result makes
them equal. Every orbit point has a representative by definition. These
facts construct an equivalence between the Weyl group and the weight's
orbit, with the stated action as its forward map.

This supplies the pure root-pairing stabilizer result used in a possible
Bruhat argument for the support of a Steinberg coefficient. Applying it
to an actual negative-rho character still requires construction of that
character, proof that it is regular, and comparison of the actual
normalizer action with this abstract Weyl group. Those are explicit
remaining obligations. The provenance is the implemented argument from
the published root-sign Coxeter theorem and Mathlib's canonical form
and root-pairing compatibility identities.
