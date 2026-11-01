# Exact classes of actual natural finite filtrations

Authors: Worker 320 (proof implementation), Worker 585 (integration and verification).

This module proves the published proposition
`Langlands.SmoothRep.FiltrationGrothendieckStatement.{uR,uG,uV,uC,vC} R G`.
The main exported theorem is
`Langlands.SmoothRep.filtrationGrothendieckStatement`. Its only outer
hypotheses are a commutative coefficient ring and a group with a topology.
The statement quantifies an arbitrary source category, a smooth functor
`F`, a finite family of smooth functors `P`, their actual natural gluing
relation, an object `X`, and finite group-algebra length of `F.obj X`.
It concludes finite group-algebra length of every `(P i).obj X` and the
exact Grothendieck class formula for their sum.

The helper theorem
`Langlands.SmoothRep.FiltrationGrothendieckProof.orderedFiltration_sum`
handles an ordered natural filtration. The implementation evaluates its
actual invariant subfunctors at `X`. Each step is bundled as a smooth
subrepresentation using the published subrepresentation construction.
The canonical inclusion into `F.obj X` is injective. Converting that
intertwiner into a group-algebra linear map lets finite length descend
to each step.

For every adjacent pair, the proof composes the actual quotient projection
with the equivariant equivalence supplied by the natural graded
isomorphism at `X`. This composite is surjective onto the given smooth
piece. The piece therefore inherits finite group-algebra length from the
upper step. The existential certificates in the conclusion are these
derived proofs; no length assumption on the pieces is supplied by the
caller.

The adjacent inclusion is injective. Its image is the kernel of the
quotient projection, and postcomposition with the graded equivalence
preserves that kernel by injectivity. Consequently these two actual maps
form a short exact sequence. The published defining exact-class relation
expresses each piece class as the upper-step class minus the lower-step
class. This uses the unchanged quotient by all actual short exact
sequences, including nonsplit ones, and requires no equivariant splitting.

The finite sum of the differences telescopes. For the initial step, the
filtration's zero endpoint gives a subsingleton carrier. The private
`zero_class` lemma applies the actual zero-map short exact sequence on
such an object and cancels to obtain its zero class. The full endpoint
has an actual bijective inclusion into the ambient representation, so
isomorphism invariance identifies the final-step class with the ambient
class. These endpoint and finite-sum calculations also apply when `n=0`:
the two endpoints coincide and the sum is empty. Repeated steps and zero
pieces require no separate assumptions.

Finally the main theorem unpacks the permutation in `IsGluedFrom`, applies
the ordered theorem, transports the length proofs along its inverse,
and uses `Fintype.sum_equiv` to recover the original indexing of `P`.

This is an internal algebraic proof derived from the published actual
filtration, smooth subrepresentation, and exact Grothendieck constructions.
It reuses Worker 320's supplied complete implementation; its endpoint and
telescoping method adapts Worker 320's earlier internal exact-class
calculation while replacing simple-factor assumptions with finite length
descended through actual maps. No new original-literature assertion is
transcribed here.

The coefficient universe `uR`, group universe `uG`, carrier universe `uV`,
and source-category object and morphism universes `uC` and `vC` remain
independent. No resizing, finite-dimensionality, irreducibility,
admissibility, exact-functor or topological-group premise is used. The
project imports consist only of the published target, actual filtration,
smoothness and subquotient interfaces, exact finite-length quotient,
integral lattice, and basic GL constructions inherited from that quotient.
No geometric-lemma, Aubert, analytic segment-classification or exhaustion
result enters the proof. Applications must separately supply their actual
natural filtration and finite length of the ambient value.
