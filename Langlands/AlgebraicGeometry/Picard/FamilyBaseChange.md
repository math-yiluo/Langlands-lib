# Actual base change of rigidified families

This module constructs pullback of rigidified line-bundle families when the
base scheme changes. It is internal infrastructure for comparison of a dual
abelian scheme with the dual of a base-changed abelian scheme.

For `b : S' → S`, an abelian scheme `A/S`, and `T/S'`,
`familyBaseChangeSpaceMap` is the canonical map

`T ×_{S'} A_{S'} → T ×_S A`.

Its first projection is the identity on the parameter `T`; its second is
the projection to `A_{S'}` followed by the base-change projection to `A`.
The map is defined by the actual scheme pullback universal property. The two
projection lemmas are the pullback lift identities.

`unitSection_baseChange_fst` proves that the unit of the existing base-changed
abelian scheme projects to `b` followed by the original unit. The proof uses
the multiplicative pullback equivalence on points and its preservation of the
identity point. `relativeSection_familyBaseChangeSpaceMap` then proves that
the displayed map respects the induced family sections, by their projections.

`familyBaseChange` applies the existing pullback functor for rigidified line
bundles to this commuting square and the identity on `T`. It preserves the
actual rigidification through the canonical structure-sheaf comparison.
`familyBaseChangeForgetIso` is the reflexive natural isomorphism identifying
its ordinary line bundle with ordinary pullback along the displayed map.

All constructions work for arbitrary schemes in the fixed universe and impose
no reducedness, noetherian or field hypothesis. This module proves no Picard-zero
stability under change of base, representability, dual comparison, equivalence
of rigidified categories, or polarization theorem. Those require further work.

## Provenance

This is internal, derived infrastructure: it combines the published actual
abelian-scheme base-change functor, relative family and induced section, and
rigidified pullback functor. The universal property of scheme pullbacks and the
proved multiplicative equivalence on base-changed points determine every map.
No desired dual, Poincare family or universal-property conclusion is supplied
as arbitrary data.
