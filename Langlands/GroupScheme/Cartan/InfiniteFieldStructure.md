# Cartan structure over every infinite field

Authors: Worker 1588 (field-local extraction and Cartan bound), Worker 1487
(published no-torus induction branch reused in this extraction).

This internal construction proves smoothness, connectedness and geometric
nilpotence of actual Cartan subgroups over every infinite field
`k : Type u`. It allows arbitrary characteristic, imperfect fields and
nonsplit witnessing tori. It supplies no finite-field conclusion and does
not prove the unrestricted `CartanStructureStatement.{u}`.

The principal construction
`IsCartanSubgroup.nilpotenceBoundOfInfiniteField` chooses a natural-number
bound for the lower central series of the Cartan's points over every
relative scheme test. The existence theorem and the specification retain
the exact predicate `HasUniformNilpotentPoints C d`; no minimality is
asserted. The bound is obtained from the actual central maximal-torus
quotient and its unipotence, rather than assuming geometric maximality
after a field extension.

## The infinite-field no-torus theorem

The proof of
`HasNoNontrivialClosedTorus.isUnipotent_of_infiniteField` extracts the
infinite-field branch of the published `noTorusStructuralReduction`
implementation. It supplies all four structural inputs with their actual
published proofs: `nilpotentCentralTorusStatement`,
`Lie.semisimpleCentralizerSmooth`,
`Lie.semisimpleCentralizerSpanning` and
`semisimpleIsogenyReduction`. The theorem has no retained structural
premise. Its only torus assumption is that every actual closed torus
inclusion has trivial all-test range.

The proof uses strong induction on the Lie dimension of a smooth
connected affine group over the fixed infinite field. The isogeny
reduction gives a smooth connected affine target and lifts its closed
tori up to isogeny. The absence of closed tori therefore passes to that
target. If it is geometrically nilpotent, nilpotence reflects through the
finite homomorphism, and the published nilpotent central-torus structure
theorem gives unipotence of the original induction group.

In the other case, the target has a geometric noncentral semisimple
tangent element. Over the infinite ground field the rational-existence
part of the published spanning theorem supplies a semisimple element
with a proper tangent centralizer. The proof chooses an actual closed
representative of its all-test centralizer, whose smoothness follows
from the published smooth-centralizer theorem. Its identity component
has smaller Lie dimension than the target, which has the same Lie
dimension as the original induction group. That component has no
nontrivial closed tori and is unipotent by induction.

The chosen tangent element is nonzero, since the tangent centralizer of
zero (written `1` in the multiplicative actual Lie-kernel notation) is
the whole Lie module. The published nonunipotence theorem for the
identity component of this centralizer contradicts its unipotence.
Neither geometric maximal-torus existence over finite fields nor the
algebraically closed trivial-maximal-torus input is used in this
induction branch.

## The Cartan conclusion

For a `CentralMaximalTorusQuotientData G`, the quotient is smooth,
connected and affine, and every torus homomorphism into it is trivial.
Thus it satisfies the closed-torus hypothesis of the new infinite-field
theorem. This proves
`CentralMaximalTorusQuotientData.isUnipotent_of_infiniteField`.

For an actual Cartan embedding `j : C → G` in a smooth connected affine
group, `hj.centralTorusQuotient` constructs such data with source `C`.
The published central-extension theorem then supplies the uniform
all-test bound. The geometric-point adapter gives exactly
`IsNilpotentGroupScheme C`, and `hj.smooth_connected` supplies smoothness
and connectedness without prior assumptions on `C`.

The provenance is internal. The field-local induction adapts Worker
1487's published implementation and uses the named Library theorems at
each step. The remaining constructions apply published actual-quotient
and central-extension interfaces. No new external structural assertion
is assumed, and no maximal-torus preservation theorem under field base
change is used. The finite-field case remains a separate obligation of
the parent task.
