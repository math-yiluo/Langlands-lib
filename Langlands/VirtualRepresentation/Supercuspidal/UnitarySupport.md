# Actual unitary supercuspidal support in the integral lattice

Author: Worker 24.

This derived construction restricts the published actual multiset support
encoding to supercuspidal terms with explicit unitarizability witnesses.
Henniart 2000, section 1.9, printed p.443, describes supercuspidal support in
the free integer module on positive-rank supercuspidal classes. In sections
2.4–2.5, printed pp.445–446 (PDF pages 7–8), the factors for the automorphic
generator are unitary supercuspidal classes, whose sum defines that generator.
Registered source: `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The original passages were read, including the displayed formulas on p.446.
The elementary implementation below transports given support witnesses; it
does not prove Theorem 2.4 or construct the absolute global generator map.

For any prime `p`, p-adic field `F : PadicField p` and compatible topological
data `T`, `CuspidalDatum.IsUnitary` is the existing descended unitarizability
predicate on its actual supercuspidal class. This means existence of an
invariant positive definite Hermitian form on an actual representative.
`UnitaryCuspidalDatum T` is the corresponding subtype. The datum retains
its positive general linear group rank. The field universe `uF` and carrier
universe `uV` are independent, and the topology is exactly `T.topology`.
No finite dimension, norm or topology is imposed on representation carriers.

`T.unitaryCuspidalDatumBasisEquiv` restricts the existing actual class
equivalence to these unitary subsets. Its inverses are the existing inverse
maps with the same unitary proofs; subtype extensionality proves the inverse
laws. The underlying-class and rank formulas are definitional.

`T.unitarySupportLattice` sums the multiplicity-one generators of these
actual unitary classes in the existing `Supercuspidal.UnitaryLattice`.
Its zero, addition, singleton and cons laws are proved. Multiset induction
computes each coefficient as the exact count cast to the integers.
Injectivity then follows from multiset extensionality and injectivity of the
natural-to-integer cast. Nonnegative counts prove effectiveness.

The ambient inclusion of this encoding equals `T.supportLattice` of the same
multiset after forgetting the unitary proofs. Multiset induction proves the
identity using the existing coefficient inclusion. Composing with the existing
ambient degree formula shows that unitary degree is the sum of the group ranks
of the terms, with every multiplicity. This is the rank of each general linear
group, independent of the dimension of a representation carrier.

`T.IsUnitaryLatticeSupport π x` is a proposition retaining a multiset of
`UnitaryCuspidalDatum T`, the existing actual normalized-induction support
relation for its underlying multiset, and equality of its encoding to `x`.
It therefore includes precisely the irreducibility and actual subquotient
witnesses required by the existing support relation. The represented `π`
has carrier universe `max uF uV`, as required by that prerequisite; the
supercuspidal terms have carrier universe `uV`. All group ranks `n` are allowed.

The implemented support lemmas recover the original relation at an encoded
multiset by injectivity, transport to ambient lattice support using the
inclusion identity, and preserve support under actual representation
isomorphisms. A witnessed unitary lattice support is effective and has
unitary degree equal to `n`; the latter is the existing ambient support degree
law applied to its inclusion.

`IsSupercuspidalSupport.exists_unitaryLatticeSupport` accepts a genuine
multiset support and an explicit unitarizability proof for every term. A
partial multiset map packages those terms in the subtype. Forgetting the
proofs recovers exactly the original multiset, so its unitary encoding
supplies the asserted support and ambient inclusion identity.

The `PadicSupercuspidal` abbreviations specialize the equivalence, additive
encoding and support relation to the actual canonical p-adic topology.
No theorem here supplies a support for an arbitrary representation, or
infers unitary supercuspidal terms merely from unitarizability of `π`.
Support uniqueness, global unitary-support existence, spanning and
correspondence compatibility remain separate theorem obligations.

The only direct import is the published
`Langlands.VirtualRepresentation.Supercuspidal.Support`, used unchanged.
This also supplies the actual support relation, class quotient, unitary
subbasis, integer lattice and Mathlib multiset infrastructure.
Development uses prepared environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
