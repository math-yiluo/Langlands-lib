# Descent of overlap-invariant tori and maximal tori

Author: Worker 1442.

This internal helper applies the published effective descent of affine closed
subgroups to tori. It works over any extension `K/k` of fields in arbitrary
universe `u`; neither field must be finite, perfect, or algebraically closed.
The ambient group scheme over `k` has an affine structure morphism.

`TorusDescent i` is the type of actual descent data for a fixed inclusion `i`
over `K`. It contains a commutative group scheme `torus` over `k`, a morphism
`inclusion` into the original ambient group, a recovery isomorphism from its
field-extension pullback to the source of `i`, proofs that the descended source
is a torus and its inclusion is closed, and the exact comparison equation
`baseChange.map inclusion = recovery.hom ≫ i`. The type itself does not assume
overlap invariance or affineness of the ambient group; these hypotheses enter
the construction of a datum.

`IsTorus.exists_descent_of_overlap_range_eq` takes an actual closed torus
in the pullback of the ambient group to `K`. Its hypothesis identifies the
images of the two pullback inclusions on every test scheme of the fpqc overlap,
after transporting the first by the ambient canonical descent isomorphism.
The result supplies a commutative group scheme `T₀` over `k`, its actual closed
inclusion `j`, and an isomorphism from its pullback to the given torus. The
pullback of `j` is exactly this isomorphism followed by the original inclusion.
The source `T₀` is proved to be a torus.

The proof applies
`IsClosedSubgroup.exists_descent_of_overlap_range_eq`, since a field-extension
map of spectra is flat and surjective. The descended group becomes a torus
after pullback, by the recovery isomorphism. `IsTorus.of_baseChange` reflects
the torus predicate, and `IsTorus.isCommMonObj` then supplies the actual
commutative group structure. Thus neither commutativity nor the torus property
is an additional descent assumption.

`IsTorus.descentOfOverlapRangeEq` uses classical choice on this existence
theorem to supply a `TorusDescent i`. For any such datum, if `i` is maximal,
`TorusDescent.isMaximalTorus_baseChange` proves maximality of its actual
pullback using the comparison equation and source-isomorphism transport.
`TorusDescent.isMaximalTorus` reflects that maximality to `k`.

`IsMaximalTorus.exists_descent_of_overlap_range_eq` additionally assumes that
the given torus over `K` is maximal. The same recovery equation and
`IsMaximalTorus.iso_comp` prove maximality of the actual pullback of `j`.
`IsMaximalTorus.of_baseChange` then proves maximality over `k`.
This uses reflection under field extension, rather than any preservation
theorem for arbitrary maximal tori.

These are derived constructions from the cited published Lean interfaces.
They form the descent step in the finite-field construction motivated by
Milne, *Algebraic Groups* (2017), Proposition 17.99 (printed pp.383–384;
PDF pp.399–400), registered as `milne-2017-algebraic-groups`. The registered
full official errata snapshot was read; it does not change Proposition 17.99.
No assertion of that proposition is used as a premise here. The all-test
overlap equality remains an explicit hypothesis: these helpers do not prove
it from Frobenius invariance or construct an invariant torus. They do not use
the no-torus unipotence theorem or maximal-torus base-change preservation.
