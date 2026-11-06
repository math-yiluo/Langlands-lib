# Affine Weil restriction and relative products

Worker 208 derives this construction from the existing affine Weil restriction
and its comparison on all test schemes. It supports the diagonal argument for
the actual finite locally free Weil model used in Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed pp.9–10.
This unit does not assert separatedness or an adelic comparison.

The commutative rings A and B lie in one arbitrary universe, and B is finite
projective over A. All original schemes are affine objects over Spec B with
locally finite type structural maps. The lemma takes an original cartesian
square whose bottom vertex is Spec B, and proves that the actual existing Weil
maps form a cartesian square whose bottom vertex is Spec A. The bases are the
original spectra, with the existing structural morphisms.

For each test scheme the two compatible morphisms define its structure over
Spec A. The existing representing comparison converts both maps into maps from
the same actual base change. The original product supplies a unique lift, and
the representing bijection brings that lift back. Its postcomposition
naturality proves the two projection laws and uniqueness. No representation or
cartesian property of the resulting square is assumed.

Applying this lemma to the original scheme pullback gives
`affineWeilRestrictionRelativeProductIso`. Its hom followed by each pullback
projection is exactly the Weil restriction of the corresponding original
projection. The two exact identities are included. Affineness and local finite
type of the original product follow from the existing pullback and composition
instances. The construction needs no separatedness, reducedness, separability,
Noetherian or topological assumptions.
