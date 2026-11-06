# Reduction of degree-zero exact classes to irreducibles

Worker 1727 derives these algebraic helpers from the published exact
Jordan–Hölder realization theorem. The group and representation-carrier
universes are independent, and the group carries its supplied topology.

`reducedClass` subtracts the actual integer degree times the trivial
continuous character-line class. It is integer linear and fixes the
genuine degree-zero kernel. If a submodule contains the reductions of all
actual continuous irreducible representations, then it contains every
reduced exact class: surjectivity of `realizeExact` supplies a finite
integral irreducible expansion, and induction on this finite combination
uses closure under addition and integer multiplication. The final lemma
therefore includes the entire degree-zero kernel in that submodule.

This is an internal derived reduction for the common-closure generation
proof. It does not assert finite Brauer induction, finite-image reduction,
or generation by character inductions. Its use of Jordan–Hölder
coefficients is through the already published
`Langlands.VirtualRepresentation.Weil.ExactRealizationProof`; it does not
replace the exact quotient with a split representation group.

The twist identity expands reduction after a character twist as the twist
of the reduction plus the original degree times the difference between
that character line and the trivial line. It follows from the proved
degree-preserving twist map, its linearity, and its action on character
lines. A submodule stable under such twists and containing all these
line differences therefore contains the reduced twist of each class
whose reduction it contains.

The final conditional lemma combines this identity with the irreducible
reduction: if every continuous irreducible is isomorphic to a character
twist of a continuous finite-image representation, and reduced
finite-image classes lie in the supplied submodule, then the full exact
degree-zero kernel lies there. These hypotheses remain explicit; this
module alone does not prove the common-closure generation assertion.
