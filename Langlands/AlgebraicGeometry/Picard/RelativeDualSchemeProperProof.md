# Properness of the chosen dual parameter scheme over a quasi-separated base

## Statement proved

`Langlands.AbelianScheme.relativeDualSchemeProper` proves the published statement
`Langlands.AbelianScheme.RelativeDualSchemeProperStatement.{u}`. That statement says:
for every scheme `S` whose underlying space is quasi-separated, every abelian scheme
`A` over `S`, and every `hA : HasDualScheme A`, the structure morphism
`(dualScheme A hA).hom` of the actual chosen dual parameter scheme is proper
(`IsProper`). The proof holds in an arbitrary universe `u` and adds no hypotheses.

## Proof

The proof is one application of the published assembly
`relativeDualSchemeProper_of_prerequisites` from the module
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeProperReduction`. That assembly
takes a record `RelativeDualSchemeProperInputs.{u}` with three fields. The proof fills
each field with a published theorem:

- `finitePresentation`: `relativeDualSchemeFinitePresentation`
  (module `...Picard.RelativeDualSchemeFinitePresentationProof`). It proves that
  `(dualScheme A hA).hom` is locally of finite presentation.
- `quasiCompact`: `relativeDualSchemeQuasiCompact`
  (module `...Picard.RelativeDualSchemeQuasiCompactProof`). It proves that
  `(dualScheme A hA).hom` is quasi-compact over a quasi-separated base.
- `valuativeExistence`: `relativeDualSchemeValuativeExistence`
  (module `...Picard.RelativeDualSchemeValuativeExistenceProof`). It proves the
  existence part of the valuative criterion for `(dualScheme A hA).hom`.

Inside the assembly, the published unconditional theorem `relativeDualSchemeSeparated`
gives separatedness. Mathlib's `UniversallyClosed.of_valuativeCriterion` turns
quasi-compactness and valuative existence into universal closedness. Local finite
presentation implies local finite type. Separated, universally closed and locally of
finite type together are the fields of Mathlib's `IsProper`.

## Dependencies

All inputs are published Library theorems. The proof does not change the statement
module `Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeProperStatement` or any
module it imports.
