# Unitary lattice support from actual normalized induction factors

Author: Worker 24.

This internal derived construction connects supplied actual normalized induction
factors to the published unitary supercuspidal lattice. It uses the existing
actual supercuspidal classes, normalized product induction, multiset support
relation and integral encoding, without changing their definitions.

For any prime `p`, actual `F : PadicField p`, compatible topological data `T`,
and ordered positive block shape `B` of total group rank `n`, the inputs are
actual supercuspidal objects `σ i` of `GL_(B.size i)(F)` and a separate
`IsUnitarizable` proof for each factor. This predicate means existence of an
invariant positive definite Hermitian form. The field universe `uF` and factor
carrier universe `uV` are independent. All group topologies are those supplied
by `T.topology`. The carriers have no imposed norm, topology or finite dimension.

`T.blockCuspidalDatum` records each factor's positive group rank and genuine
supercuspidal isomorphism class. `T.blockUnitaryCuspidalDatum` adds its supplied
unitary proof; the class predicate reduces to the actual object's predicate by
the published quotient definition.

`T.unitaryInductionSupport` applies the existing `unitarySupportLattice` to the
entire finite family, regarded as a multiset. Its coefficient at any actual
unitary class is exactly that class's count, cast to the integers. Ambient
inclusion equals the ambient lattice encoding of the same underlying actual
class multiset. Effectiveness follows from nonnegative counts, and degree is
`n`, by the existing rank-sum formula and `B.sum_eq`. No factor or multiplicity
is omitted. These constructors and formulas include the empty shape at rank
zero. Degree always counts general linear group ranks, independently of
carrier dimensions.

`unitaryInductionSupport_eq_of_iso` proves invariance under componentwise
actual isomorphisms of the supplied supercuspidal objects. Their quotient
classes are equal; congruence and subtype extensionality identify the unitary
data families and hence their encoded sums. In particular, choices of proof of
unitarity do not affect the encoding.

`isUnitaryLatticeSupport_of_normalizedProductEquiv` also accepts an actual
irreducible smooth representation `π` with carrier universe `max uF uV` and an
actual representation equivalence from `π` to the full normalized product of
the supplied factors. The cuspidal shape of the constructed data is
definitionally `B`, by structure eta and proof irrelevance. The equivalence
gives an injective intertwiner into the existing smooth induced object and
therefore an actual subquotient witness. The supplied factors represent their
own quotient classes. These data give the existing supercuspidal support
relation, whose unitary multiset encoding is the asserted lattice support.
This is an intrinsic witness construction; it does not use a classification
theorem.

Henniart 2000, sections 2.4–2.5, printed pp.445–446 (PDF pages 7–8), motivates
this adapter: the genuine unitary supercuspidal factors in Theorem 2.4 supply
the integral automorphic sum in section 2.5. The original passage was read in
the parent task, including the displayed sum. Registered source
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The generic packaging here is internally derived, rather than a separately
numbered result attributed to that source. Existence of such factors for
associated global objects, support uniqueness and the global generator map
remain separate obligations. Unitarity of `π` alone is not a hypothesis that
supplies unitary factors.

The sole direct import is the unchanged published
`Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport`. Development
uses prepared environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
