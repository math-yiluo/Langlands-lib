# Etale and fppf Picard class sheaves over a field

`Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement.{u}`
is an internal geometric proof target for the actual relative Picard sheaf.
For every field `k : Type u` and every
`X : Over (Spec (CommRingCat.of k))`, it states that properness of `X.hom`
implies

```text
Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of k)))
  (RelativePicard.etaleClassSheafPresheaf X.hom).
```

The imported presheaf is the published etale sheafification of ordinary
line-bundle isomorphism classes on the actual fibre products `T ×_k X`.
The sheaf condition uses the whole category of schemes over `Spec k`.
It includes arbitrary nonreduced and non-quasi-compact test schemes and all
sections of the etale sheaf, including sections without a global line-bundle
representative. It does not restrict the comparison to field-valued points
or to actual bundles.

The only geometric hypothesis is properness over the field. No projectivity,
smoothness, reducedness, connectedness, rational point, chosen section,
equality of global functions with `k`, or Picard representability appears.
The universe `u` remains arbitrary, and the sheaf takes values in
`Type (u + 1)`.

## Canonical comparison

The lemma `RelativePicard.etaleToFppfClassSheaf_isIso_iff` applies to every
scheme morphism `f`, without properness or a field hypothesis. It proves that
the displayed fppf sheaf condition is equivalent to invertibility of the
published canonical map `RelativePicard.etaleToFppfClassSheaf f`.
For the forward direction of this equivalence, an invertible comparison
identifies its source presheaf with the underlying presheaf of the actual
fppf class sheaf; the sheaf property transports across that isomorphism.
For the reverse direction, the published
`RelativePicard.etaleFppfClassSheafIso` supplies an isomorphism whose forward
map is exactly the canonical comparison.

Consequently, a proof of the field statement would give a natural isomorphism
of the two actual sheafifications on all test schemes, compatible with their
units by the already published formulas. An unspecified equivalence of
point sets would not supply this conclusion.

## Provenance and proof obligation

This proposition records the missing fppf descent hypothesis of the published
internal module `Picard.EtaleFppfSheafComparison` in the proper-field case.
It is an internal target, rather than a direct translation of an external
representability theorem. Worker 509 identified the missing comparison in the
Picard-stack route; Worker 144 supplied this statement and the formal
invertibility criterion.

The criterion uses only the published comparison isomorphism and invariance
of the sheaf property under presheaf isomorphisms. The field proposition is
defined here and remains to be proved. This module proves no proper-field
descent, Picard algebraicity, or scheme representability. The intended
prerequisite proof must establish the field proposition without using either
of the latter conclusions as an input.
