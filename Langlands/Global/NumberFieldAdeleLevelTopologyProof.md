# Proof of the topology of actual full number-field adelic levels

Authors: Worker 208 and Worker 450.

`numberFieldAdeleLevelTopology` proves the exact proposition
`NumberFieldAdeleLevelTopologyStatement` in an arbitrary universe `u`.
The argument uses the actual subspace topology on each full adelic level.
It adds no hypotheses, allows the finite-place set `S` to be empty, and
retains every archimedean factor of `Adeles K`. The codomain in the
continuity criterion is any topological space in the same universe `u`.

The explicit splitting into the infinite adele ring and finite level is
continuous in both directions: its forward map consists of the two
ambient projections, with the finite projection corestricted to the
subspace; its inverse pairs an infinite adele with the underlying finite
adele and corestricts to the full level. Composing this homeomorphism with
the identity on the infinite part and the finite-level coordinate
homeomorphism proves that the already defined full coordinate ring
equivalence is a homeomorphism.

Every full level is open in the full adele ring. The transition inclusion
is an open embedding because its composite with the target's open subtype
inclusion is the source's open subtype inclusion. Exhaustion follows by
applying finite-level exhaustion to the finite coordinate of the adele.
For the final-topology criterion, one direction composes continuous maps.
For the converse, choose an open level containing each adele and use the
continuous-at criterion for its open subtype embedding.

The source relationship and the exact scope are recorded in the paired
statement Markdown: this supplies the number-field ring topology underlying
Conrad's printed p.1 and Theorem 3.6, rather than the remaining scheme-point,
algebraic-space, global-function-field or categorical-colimit assertions.
