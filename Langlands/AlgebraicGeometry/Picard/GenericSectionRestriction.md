# Restriction of sections to a generic point

This internal adapter defines restriction on actual scheme morphisms.
For an integral scheme `S` and a morphism `p : X ⟶ S`,
`genericSectionRestriction p` sends a section `s` with `s ≫ p = 𝟙 S`
to the composite of `s` with
`S.fromSpecResidueField (genericPoint S)`. The codomain retains the
condition that this composite is over `S`, using the actual generic
residue-field map. Both domain and codomain are subtypes of scheme
morphisms, rather than isomorphism classes.

`hom_ext_of_genericPoint` proves a slightly more general uniqueness
statement. Two maps `f g : S ⟶ X` with equal composites to `S` are equal
when `p` is separated and their generic residue-field restrictions agree.
The proof applies Mathlib's `ext_of_fromSpecResidueField_eq` to the
singleton containing `genericPoint S`. This singleton is dense by
`genericPoint_closure`, and integrality supplies the reducedness required
by that extensionality theorem.

`genericSectionRestriction_injective` applies this uniqueness statement
to sections. Their composites to `S` are both the identity; equality of
the restricted subtype elements gives equality of their underlying
generic morphisms, and subtype extensionality finishes the proof.

The provenance is internal: this is the direct specialization of
Mathlib's dense-point extensionality theorem to an integral scheme's
generic point, together with composition of the canonical scheme maps.
The universe is arbitrary. No noetherianity, valuation rank, finite-type
or geometric-unibranch assumption is needed for uniqueness. Existence of
an extending section and extension of line bundles remain separate
obligations.
