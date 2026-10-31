# Irreducible quotients of a juxtaposed socle product

Authors: Worker 167 and Worker 1032.

This internal supporting module identifies every irreducible quotient of a
two-block juxtaposed segment-socle product with the actual singleton union
datum. It assumes `SegmentZelevinskyConstituentExistence` explicitly. It does
not prove that existence proposition, the length-two filtration, or uniqueness
of the original product's irreducible submodule.

`LengthCriterionProof.quotientTopMap` is the actual equivariant projection
from an arbitrary representation `ρ` to `quotientRep K ⊤`. The latter is the
successive quotient model: first restrict to the top invariant subspace, then
divide by the pullback of `K`. The projection sends `v` to the quotient class
of `⟨v, mem_top⟩`. It is a linear map by composition of the codomain restriction
of the identity with `mkQ`; equivariance is definitional. The theorem
`quotientTopMap_surjective` chooses a representative of each quotient class.
This construction is valid over any field, monoid, and representation carrier.

`JuxtaposedShuffle.exists_juxtaposedUnionHead` takes the explicit constituent
existence premise, an actual datum `d` of length two, strong segment socles on
its supplied blocks, precedence of segment 1 before segment 0, and
juxtaposition of these segments. It first returns the adjacency identity:
the base of segment 0 is the base of segment 1 twisted by segment 1's length.
It also produces a union segment `U`, an optional intersection `I`, and an
actual segment-product datum `e` of the original total degree, with:

- the union/intersection replacement relation in the original factor order;
- `List.ofFn e.segments = U :: I.toList` and `e.HasSegmentSocles`;
- irreducibility of `e.induced.representation` and `e.length = 1`;
- for every segment of `e`, base equal to original segment 1's base and
  length equal to the sum of the two original lengths;
- for every invariant `K` for which `quotientRep K ⊤` is irreducible, a
  nonempty type of actual representation equivalences from that quotient to
  `e.induced.representation`.

The construction chooses `I = none`. The statement deliberately exposes an
optional segment to match the parent theorem's replacement interface.

For the proof, choose a representative `A` of the earlier base `ρ`, and write
the later and earlier lengths as `q` and `l`. Adjacency and the original degree
sum give total degree `(q + l) * ρ.rank`. Define `U` with base `ρ` and length
`q + l`. The replacement lemmas from `JuxtaposedUnionDatum` identify this
explicit segment with the union and certify the empty intersection. Apply the
explicit constituent-existence premise to `U` to obtain an actual strong
socle `π` and its strong-head property for decreasing induction. Package `π`
as `e` using `SegmentProductDatum.ofSingleSegment`; the supplied one-block
induction equivalence identifies `e.induced` with `π`.

The supporting theorem `exists_surjective_from_decreasing` supplies an actual
surjection from the full decreasing induction of `U` to `d.induced`. For any
irreducible `quotientRep K ⊤`, compose this surjection with `quotientTopMap`.
The strong-head comparison
`IsIrreducibleHead.nonempty_equiv_of_quotient_of_surjective` identifies this
quotient with `π`. Composition with the inverse one-block equivalence gives
the claimed equivalence to `e.induced`. Thus no head assertion about the
two-block product is added as a hypothesis, and existence of an irreducible
quotient of that product is not asserted by this module.

The field and original segment-carrier universes remain independent as `uF`
and `uV`. Actual induced carriers have universe `max uF uV`, as in the
published definitions. The supplied topology is always `T.topology`.

The provenance is an internal deduction from the two supporting constructions
and the general successive-quotient model. The decreasing quotient uses only
ordered normalized-product regrouping, twist and representative equivalences,
and surjectivity of normalized induced maps, together with the explicit
constituent-existence premise. The union datum uses the published
`cuspidalIntegralTwistFreeness` proof from task
`67279e36-f3c2-42e3-9302-11729784042e`, interval calculations, and one-block
induction. The strong-head comparison uses actual quotient kernels and
canonical constituents. `LengthCriterionProof` supplies only the general
successive-quotient definitions used here.

A recursive audit of the 157 project modules in this module's import closure
found no excluded linked-product or reverse-product conclusion, quotient-Hom
proof, product criterion, commutation, gluing, multisegment existence or
exhaustion, quotient coverage, square-integrable classification, or derivative
proof. The individual-segment existence statement is an explicit premise,
not an imported proof. This conditional supporting result does not discharge
the unconditional exact-target obligation of the parent task.
