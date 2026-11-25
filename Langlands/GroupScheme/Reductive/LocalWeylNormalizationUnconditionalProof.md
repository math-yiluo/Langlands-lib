# Weyl normalization over reduced local rings

`Langlands.GroupScheme.LocalSplitCell.localWeylNormalization.{u}` proves exactly
`Langlands.GroupScheme.LocalSplitCell.LocalWeylNormalizationStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

Over every reduced local commutative ring, for the reductive group, closed fibrewise maximal split torus, fibrewise root datum and base in the statement, each supplied simple-root parametrization has an opposite-root parametrization making its Weyl point act by the simple reflection. All ring, torus-index and root-index universes remain exactly those of the published proposition.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.localWeylNormalization_of_field` from
  `Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof`.
- `Langlands.GroupScheme.LocalSplitCell.fieldWeylNormalization` from
  `Langlands.GroupScheme.Reductive.LocalWeylNormalizationField`.

The proof supplies the published field-normalization theorem to the ring-level reduction. That reduction computes a rescaling unit from a big-cell coefficient over the dual numbers, identifies it on field fibres, and uses reducedness to check the resulting Weyl action over the ring.

The complete proof term is:

```lean
localWeylNormalization_of_field fieldWeylNormalization
```

This is an internal derived proof assembling existing Library results along the route above. The target statement and its imports are unchanged.
