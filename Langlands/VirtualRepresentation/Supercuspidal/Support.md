# Actual supercuspidal support in the integral lattice

Author: Worker 24.

This construction transports the published multiset support relation to the
published integral lattice on the same actual supercuspidal isomorphism classes.
Its provenance is Henniart 2000, section 1.9, printed p.443 (PDF page 5),
registered source `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The retained original page was read and its displayed formula inspected.
Henniart regards supercuspidal support as an element of the free integer module
on the disjoint union of supercuspidal classes over positive ranks.

The Lean constructions and their elementary coefficient proofs are derived
infrastructure implementing that encoding. They use the actual support relation
of `Langlands.Representation.Classification.SupercuspidalSupport` and the actual
basis of `Langlands.VirtualRepresentation.Supercuspidal.Basic`. The support
relation asks for an irreducible subquotient of an actual normalized parabolic
induction with the stated multiset of supercuspidal factors.

For every prime `p`, p-adic field `F : PadicField p`, and compatible topological
data `T : F.TopologicalData`, `T.cuspidalDatumBasisEquiv` identifies a datum
consisting of a positive natural rank and a genuine supercuspidal class with
the dependent union of those same classes indexed by positive integers. Both
inverses only unpack the structures; they do not choose representatives.
The field universe `uF` and representation-carrier universe `uV` are independent.
The topology throughout is exactly `T.topology`.

`T.supportLattice` is an additive map from multisets of these data to the
integer lattice, obtained by mapping each datum to its basis generator and
summing the multiset. The zero, sum, singleton and cons identities are proved.
`supportLattice_apply` proves that the coefficient at a datum is its multiset
count cast to the integers. Multiset induction proves this formula, and
injectivity of the integer cast and multiset extensionality give
`supportLattice_injective` and `supportLattice_eq_iff`. Thus equal lattice
encodings imply equal multisets, without asserting uniqueness of supports of a
representation.

`supportLattice_effective` follows from nonnegative counts and surjectivity of
the class equivalence. `supportLattice_degree` is proved by multiset induction
and evaluation of the integral degree on a generator. Its value is the sum of
the group ranks, with all multiplicities. Rank means the size of the general
linear group; representation carriers are not required to be finite dimensional.

`T.IsLatticeSupport π x` is a proposition: some actual multiset support `s` of
`π` has `T.supportLattice s = x`. The implemented lemmas transport witnessed
multiset supports to this relation, recover the original relation at an encoded
multiset using injectivity, and preserve lattice support under isomorphisms of
actual smooth representations. A witnessed lattice support is effective and has
degree equal to the rank `n` of `GL_n(F)`, by the published support rank-sum law.
The represented `π` has carrier universe `max uF uV`, as in the prerequisite
normalized induction construction; individual supercuspidal classes retain
carrier universe `uV`. All `n`, including zero, are allowed.

The `PadicSupercuspidal` namespace supplies the same equivalence, additive map
and proposition for `F.canonicalTopologicalData`, directly in the canonical
p-adic lattice.

This module proves no existence or uniqueness theorem for supercuspidal
supports, chooses no unconditional support, and makes no claim about unitary
support, decomposition of arbitrary representations, lattice spanning or a
correspondence. Those require separate theorem inputs.

The two project dependencies are imported without modification. The only
additional Mathlib infrastructure is multiset sums and counts. Development
checks use the prepared environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
