# Fixed units and the field norm

Author: Worker 42.

This pair supplies the field-specific identification needed to interpret
degree-zero Tate cohomology. It uses the actual representation from
`Cohomology` and Mathlib's existing algebra norm. It neither defines a
new field norm nor constructs a reciprocity map.

`baseUnitsToInvariants` is the actual inclusion of base-field units into
the invariant part of the extension's unit representation, written
additively. Its membership certificate is `baseUnit_fixed`: every
base-field algebra automorphism fixes the image of a base-field element.
The map is injective by injectivity of the algebra map on fields.

For a finite Galois extension, `baseUnitsToInvariants_surjective` uses
Mathlib's fixed-field theorem to recover a base-field element from an
invariant extension unit. The element is nonzero because its image is a
unit, so it yields an actual base-field unit. `baseUnitsEquivInvariants`
packages this proved bijective additive homomorphism as an equivalence.
Its application equation fixes the direction and the embedding used.
No fixed-field equivalence is assumed as an input.

`unitsRepresentation_norm` identifies the representation-theoretic norm,
the sum of the automorphism operators in additive notation, with the
existing field norm on units followed by inclusion. The proof unfolds
the lifted-integer representation and invokes Mathlib's product formula
for the norm of a finite Galois extension. Thus the norm image used in
the Tate quotient is the ordinary field-norm image. A choice of finite
enumeration of the actual Galois group is explicit in this identity.

The base field and extension have independent universes. The scalar
ring remains the explicitly lifted integer ring used by `Cohomology`.
There is no resizing of either field, and no local-field, cyclicity,
class-formation, or reciprocity hypothesis.

This pair is an intrinsic bridge for the later degree-zero comparison.
It does not by itself identify the actual Tate complex's homology with
a quotient, nor supply the degree-minus-two abelianization comparison
or a cup-product isomorphism.

## Sources and declaration correspondence

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67, 1979,
source `serre-1979-local-fields`, retained at
`C:/Central-Library/Serre--Local Fields--1979.pdf`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`:

- Chapter VIII, section 1, printed pp.127–128 / PDF pp.133–134:
  the norm operator on a finite-group module and degree-zero Tate
  cohomology as invariants modulo its norm image. This motivates
  `unitsRepresentation_norm`.
- Chapter XI, section 1, printed pp.164–165 / PDF pp.170–171:
  the multiplicative Galois formation and its fixed coefficient
  groups. This is the setting for `baseUnitsEquivInvariants`.
- Chapter XI, section 3, printed p.169 / PDF p.175, and Chapter XIII,
  section 4, printed p.195 / PDF p.200: the norm quotient in the
  degree-minus-two reciprocity specialization and its application
  to actual local-field multiplicative groups. The reciprocity
  isomorphism itself is not asserted here.

The implemented intrinsic proofs use pinned Mathlib's
`IsGalois.mem_range_algebraMap_iff_fixed`,
`Algebra.norm_eq_prod_automorphisms`, and the actual definitions
`Representation.invariants` and `Representation.norm`.
The base-unit inclusion and its fixedness are from `CyclicClass`;
the coefficient representation is from `Cohomology`.
