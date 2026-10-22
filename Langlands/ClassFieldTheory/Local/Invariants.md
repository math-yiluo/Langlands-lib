# Actual local invariant families and arithmetic normalization

`InvariantFamily` contains additive homomorphisms from actual continuous
absolute `H²` and actual finite relative `H²` to the quotient `Q/Z`.
It contains no mathematical laws. In particular, neither existence of a
normalized family nor any isomorphism or class-formation theorem is an
input to its construction. The separate predicates are intended for
existential proposition targets.

`AbsoluteIsomorphisms` asserts bijectivity of the absolute maps.
`RelativeImages` asserts injectivity of every relative map and identifies
its image with the subgroup annihilated by the actual extension degree.
This subgroup is `(1/[L:K])Z/Z` inside the actual rational quotient.

`IsArithmeticUnramifiedCoordinate` tests an explicit cyclic coordinate
`chi : Gal(L/K) ≃* Multiplicative (ZMod n)`. It requires the existing actual
residue action to be injective (trivial inertia), and the automorphism with
coordinate `+1` to act on the actual residue field by its base cardinality
power. All residue rings and the action come from the published
`LocalGalois.residueHom` construction with the canonical spectral norm on
the base. No supplied residue map, abstract cyclic Galois group, or
assumed Frobenius classification is used. This is a predicate on test
data, not a construction or existence assertion for unramified extensions.

`ArithmeticNormalization` requires the explicit positive carry class
`cyclicClass chi a` to have invariant `+1/n` whenever the coordinate
passes that arithmetic test and `a` has canonical additive order one.
The order is the existing `canonicalTopologicalData.ord`; the field
element is a unit, so its zero convention cannot interfere. This reuses
the valuation-normalization construction without reproving its separate
normalization theorems. The explicit positive sign is justified by
`cyclicCarry_rational`, which identifies the carry with the differential
of the rational lift of the generator character.

`AbsoluteRestriction` asserts the multiplication-by-degree formula for
the actual continuous cohomology restriction map. The fields carry
compatible specified algebras over `Padic p`, and the algebras on their
actual algebraic closures are explicit. The input is not a homomorphism
with a prescribed effect on invariants.

These definitions leave finite-to-absolute comparison, corestriction,
and the complete simultaneous realization theorem as separate work.
They do not identify finite cohomology with continuous cohomology by a
type alias. They do not define the desired invariant by an unproved
choice. In particular this pair, or its compilation, does not establish
local class field theory.

The base fields have arbitrary universe `u`; the finite relative
extensions have independent universe `v`. The absolute restriction API
currently relates base fields in the same arbitrary universe, matching
the concrete closure map used by `Cohomology`. There is no restriction to
`Type 0`, nor any implicit resizing of fields.

## Sources and convention

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67, 1979,
registered source `serre-1979-local-fields`, retained at
`C:/Central-Library/Serre--Local Fields--1979.pdf`:
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

* Chapter XIII, section 3, Proposition 6 and the following explicit
  formula, printed p.193 / PDF p.198: the invariant is an isomorphism,
  given by normalized valuation, the inverse connecting map, and
  evaluation at arithmetic Frobenius.
* Proposition 7 and Corollary 2, printed pp.193–194 / PDF pp.198–199:
  restriction multiplies by the extension degree, and the finite
  relative image is exactly `(1/n)Z/Z`.
* Chapter VIII, section 4, printed p.133 / PDF p.139: the character
  attached to the chosen cyclic generator takes value `1/n`; its
  connecting class determines the periodicity convention.
* Chapter I, section 7, printed pp.20–22 / PDF pp.28–30, and Chapter
  XIII, section 2, printed pp.190–191 / PDF pp.195–196, especially
  example (a) on p.191: the residue action, inertia, and arithmetic
  Frobenius convention.

Serre's fundamental class has invariant `+1/n`. The inverse of his
degree `-2` cup-product is arithmetic reciprocity (Chapter XI, section 3,
printed pp.168–169 / PDF pp.174–175; Chapter XIII, section 4, Proposition
8, printed p.196 / PDF p.201). Henniart, *Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique*, Inventiones 139 (2000),
section 1.1, printed p.439 / PDF p.1, instead normalizes the map from the
Weil group to field units to send geometric Frobenius to a uniformizer.
Its inverse convention on field units is the pointwise inverse of
Serre's arithmetic reciprocity. Replacing a fundamental class by its
negative reverses the cup-product convention. These directions and signs
must remain explicit in the later Tate targets.

The Henniart source is registered as `henniart-2000-simple-proof`,
SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
retained at
`C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.

## Declaration dependencies

`Cohomology` supplies the actual coefficient modules, cohomology groups,
quotient `Q/Z` and absolute restriction. `CyclicClass` supplies the explicit
cocycle and class; neither defines the invariant by choosing an unproved
existence theorem.

The published local-field inputs are `LocalField.Definitions`, artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` v1, and `LocalField.Canonical`,
artifact `c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629` v1. Canonical realization is
therefore constructed for every `PadicField`, not assumed. Canonical order
comes from `LocalField.Normalization.Definitions`, artifact
`e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2` v1. Actual residue action comes from
`Galois.Local.SpectralDefinitions`, artifact
`82bd181d-11b1-4000-afb6-1acdb762dd32` v1. The latter two effective pairs
were checked unchanged and current at Library commit
`5bc58c2525e0499012801c80f17b6a9c04d57263`.
