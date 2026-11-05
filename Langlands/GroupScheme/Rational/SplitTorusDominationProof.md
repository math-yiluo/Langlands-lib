# Unipotent splitness from pointed split-torus domination

`unipotentSplitTorusDomination` proves the exact proposition
`UnipotentSplitTorusDominationStatement.{u}`. For every field in the arbitrary
universe `u`, a smooth connected affine unipotent group with an actual pointed
dominant morphism from a finite-rank split torus has a finite represented
additive series over the same field. The statement and its existing
`IsUnipotent`, `HasPointedSplitTorusDomination`, and
`RelativeRoot.IsSplitUnipotent` predicates are unchanged.

The proof first establishes `primeExponentSplitTorusDomination`, the
commutative prime-exponent case over the original field. Affineness of the
structure morphism over the affine field spectrum gives affineness of the
group. The theorem
`AffineCoordinates.exists_finite_corepresented_primitive_generators_of_smooth_uniformExponent`
then supplies a finite set of primitive functions generating its coordinate
algebra. This theorem derives the generators from smoothness, commutativity,
and the exponent on all relative scheme tests. Its implementation passes to
an algebraic closure, obtains reduced finite-type coordinates and the
convolution exponent, applies primitive generation there, and faithfully
descends generation by the primitive-defect kernel. The returned generators
and their generation property are over the original field.

`isSplitUnipotent_of_pointed_finitePrimitiveGenerators` applies the supplied
pointed domination to these generators. It transports to the canonical
affine model, obtains reducedness from smoothness and connectedness, and
uses pointed Laurent pullback and primitive polynomial coordinates to obtain
an actual vector-group isomorphism over the ground field. The existing
vector-group series gives the required represented additive series on the
original group.

Finally, `unipotentSplitTorusDomination_of_primeExponent` consumes this proved
elementary case. Its derived-subgroup reduction reduces general unipotent
groups to commutative ones. The commutative characteristic-zero theorem
handles characteristic zero; the prime-power-image reduction uses the
elementary case in positive characteristic. Existing split-series extension
results assemble the finite series. No elementary-case or other structural
theorem remains an input of the final theorem.

Finite fields, imperfect fields, and characteristic zero are retained. The
dominating map has the original scheme-morphism meaning, with dominance and
the identity-section equation; it need not preserve multiplication or
extend across a torus boundary. The conclusion uses the existing actual
smooth connected closed normal terms and represented fppf quotients
isomorphic to the one-dimensional vector group, and includes a zero-length
series for the trivial group.

The task's source is Springer, *Linear Algebraic Groups*, second edition
(1998), Theorem 14.3.8(i) and proof, printed pp.245–246, specialized to a
unipotent target and a split multiplicative dominating source. The implemented
proof follows the elementary-factor and extension strategy through the named
Lean interfaces above. Its primitive-generation step uses the coordinate
and faithful-descent route documented by those modules. This final module
composes those results and the existing all-characteristic reductions.
