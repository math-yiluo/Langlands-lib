# Naturality of the original regular-tensor comparison

This companion proves the two whole-map naturality clauses of
`Langlands.Algebra.RegularTensorContractionTheorem`. These are intrinsic
consequences of the published original-module constructions. Comparison
existence and the closed theorem are proved in `RegularTensorContraction`.

`contraction_naturality` applies the published tensor quotient's additive-map
extensionality principle. On every pure tensor the desired equation reduces
to the original intertwiner law, with its orientation reversed.

`comparison_naturality` quantifies over arbitrary comparison witnesses in the
published interface. The forward equation follows pointwise after the actual
part inclusion, using both factorizations and contraction naturality; subtype
extensionality recovers equality in the part. Applying the inverse on the
target side and using the two appropriate bundled inverse identities then
gives the inverse equation. Both conclusions are equalities of complete
additive maps using the actual `tensorMap` and `restrictNondegeneratePart`.

The complete unapplied types of both lemmas are checked at arbitrary
independent universes and at the unequal triples `(0, 1, 2)` and `(2, 1, 0)`.
The ring and both ambient module universes are independent. No ambient
nondegeneracy hypothesis, coefficient structure, or replacement tensor action
is used. These naturality clauses are internal packaging of the canonical
comparison; Renard's displayed complex-algebra assertion is formula
(I.2.3.3), printed page 17 / PDF page 23, in the French edition dated
9 July 2026. The arbitrary idempotented-ring/additive target is an internal
generalization. The supplementary 2010 errata, PDF pages 1–2, does not alter
this contraction assertion.
