# Proof of ConnectedReductiveAdjointDeterminantStatement

`Langlands.GroupScheme.Lie.connectedReductiveAdjointDeterminant.{u}` has exactly the published proposition
`Langlands.GroupScheme.Lie.ConnectedReductiveAdjointDeterminantStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement`.

The actual rational adjoint determinant character is zero for every connected reductive affine locally finite-type group over every field.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
connectedReductiveAdjointDeterminant_of_centralDerivedProduct
    (reductiveCentralDerivedProduct_of_surjectivity derivedSubgroupRepresentability
      reductiveCentralTorusSurjectivity)
```

First discharge the central-times-derived product reduction using unconditional derived-subgroup representability and central-torus product surjectivity. Pass that inline product theorem to the published adjoint-determinant reduction, which combines central triviality with annihilation on the derived factor. No separate unpublished product proof is imported.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.Lie.connectedReductiveAdjointDeterminant_of_centralDerivedProduct` in `Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement`.
- `Langlands.GroupScheme.reductiveCentralDerivedProduct_of_surjectivity` in `Langlands.GroupScheme.Reductive.CentralDerivedProductReduction`.
- `Langlands.GroupScheme.derivedSubgroupRepresentability` in `Langlands.GroupScheme.Derived.RepresentabilityProof`.
- `Langlands.GroupScheme.reductiveCentralTorusSurjectivity` in `Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof`.

This is an internal derived proof of the existing Library proposition. The composite route is also described in the note
`notes/group-schemes/composable-targets-2026-11-08.md`.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
