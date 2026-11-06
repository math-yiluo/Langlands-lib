# Actual scheme base change with product point topologies

Worker 208 derives this comparison to retain original maps when changing the
coefficient base of an adelic model. Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Theorem 3.6 and Example 4.2, printed
pp.8–10, use independently defined product topologies at arithmetic levels.
The construction here supports comparing those topologies across a change of
model base; it does not establish the full adelic Weil homeomorphism.

A and B are commutative rings in an arbitrary common universe, with a specified
A-algebra structure on B. The value rings R i are commutative B-algebras and
A-algebras with the given scalar towers. For the topological conclusions they
are local topological rings with open unit groups. The scheme X is any actual
scheme over Spec A. No finiteness, compactness, separatedness, field or
Noetherian assumption is required on X or the coefficient bases.

`ringPointBaseChangeEquiv_changeRing` first proves that the existing
pullback-adjunction equivalence commutes with any literal map of value
B-algebras, restricting its scalar action to A on the original scheme side.
Its proof applies the inverse point equivalence and compares the first
projection to X. The exact coordinate law
`productPointMap_ringPointBaseChangeEquiv` is its specialization to the original
product coordinate projections. These two laws are algebraic and require no
topologies or local-ring assumptions.

`localFactorPointHomeomorph` is the product of the existing original
scheme-point base-change homeomorphisms, from points relative to A to points
of each actual local model. Consequently the literal coordinate restriction
map is inducing for the existing `localProductPointTopology`, which had been
defined independently using the actual local models. This observation assumes
no bijectivity of points over an infinite product for X.

`localProductPointBaseChangeHomeomorph` equips the original points over the
product ring and the points of the actual B-base change over that same ring
with their existing product-induced topologies. The original point equivalence
is a homeomorphism for these two topologies: after the inducing coordinate
maps it is the product of the existing local base-change homeomorphisms. The
coordinate law proves that this square commutes. Cancellation of inducing
maps proves the equivalence is inducing, and its established bijectivity then
proves the assertion. The apply theorem states that the resulting map is
exactly `ringPointBaseChangeEquiv`, rather than a chosen bijection with the same
source and target.
