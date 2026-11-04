# Isomorphism invariance and geometric normality of the fixed torus envelope

Worker 1436. This internal prerequisite uses the unchanged
`closedTorusEnvelope` and its actual `TorusGeneratedEnvelope`
representatives. The universe is arbitrary. The ambient groups and all
isomorphisms are group schemes over the original field.

`SubgroupFunctor.ContainsTori.comap_iso` transports containment of every closed
ground-field torus along an ambient isomorphism. The proof transports each
actual torus embedding and uses preservation of closed immersions.
`closedTorusEnvelope_eq_comap_iso` applies this to the closed subgroups in the
intersection defining the fixed envelope. Its conclusion is equality of
subgroup functors on every relative scheme, including nonreduced tests.

`TorusGeneratedEnvelope.transport` keeps the original representing group and
postcomposes its inclusion with the ambient isomorphism. The invariance
equality identifies its range with the fixed envelope in the new ambient
group. `isoOver` then constructs the actual canonical isomorphism to any
supplied representative there. Its `isoOver_hom_comp` identity says that this
isomorphism commutes with the inclusions and the ambient isomorphism.
These constructions require no smoothness, connectedness, affineness,
perfectness or restriction on characteristic.

`rational_mem_normalizer` applies invariance to inner conjugation by an
actual ground-field point and its inverse. This gives membership in the
existing all-test normalizer at the rational base test: every restriction of
that rational point normalizes the envelope on every scheme over the field.

`isNormal_of_isAlgClosed` assumes that the field is algebraically closed and
that the ambient group is reduced, affine over the field and locally of finite
type. The published normalizer representability theorem gives an actual
closed subgroup representing the full normalizer. The preceding lemma puts
every rational point of the ambient group in that subgroup. The published
algebraically closed rational-point containment theorem, applied to the
identity homomorphism of the reduced ambient group, gives containment on all
tests. The normalizer is therefore the whole group, and the envelope is
normal on every relative scheme. Neither the envelope nor its normalizer
is assumed reduced or smooth. `isNormal_of_smooth_isAlgClosed` supplies
ambient reducedness using the published smooth-over-a-field theorem.
Connectedness of the ambient group is unnecessary.

`isNormal_of_baseChange` descends full normality of the represented envelope
through any supplied flat, surjective, quasi-compact morphism of schemes.
It assumes only that the original ambient group is affine over the field.
The actual closed normalizer is represented in the original group; its
base change is the normalizer of the base-changed subgroup functor.
Normality after base change makes that normalizer the whole group.
The published fpqc reflection of containment in a represented subgroup
therefore makes the original normalizer the whole group.

`baseChangeOfEnvelopeEquality` constructs an actual representative over a
supplied extension of the base field from an explicit equality between the
base-changed fixed envelope and the fixed envelope of the base-changed
ambient group. The representing group and inclusion are exactly the base
changes of the original group and inclusion. Closedness and representation
follow from their published base-change theorems.
`isNormal_of_algebraicClosure_envelope_eq` combines this construction,
smooth geometric normality and fpqc descent. It assumes smoothness and
affineness of the original ambient group and precisely this envelope equality
for the actual algebraic-closure base change. Faithful flatness and
quasi-compactness of that field extension come from `fieldExtension_fpqc`.
The equality remains a hypothesis; the module does not prove that newly
appearing tori over the extension lie in the base-changed envelope.

The provenance is internal: these are consequences of the existing
intersection, actual representative, inner automorphism, closed normalizer
and rational-point detection constructions, together with represented
subgroup base change and fpqc containment reflection. They isolate the
geometric normality argument and its descent reduction needed by the
rational-lifting task. Compatibility of this fixed envelope with field
extension remains an obligation, so general-field normality remains
unproved; this module does not assert the full
`TorusGeneratedEnvelopeNormalityStatement` or the rational-lifting theorem.
