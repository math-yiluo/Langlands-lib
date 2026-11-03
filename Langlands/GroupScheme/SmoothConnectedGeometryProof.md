# Geometric integrality of smooth connected affine group schemes

`Langlands.GroupScheme.smoothConnectedAffineGeometry.{u}` proves exactly
`Langlands.GroupScheme.SmoothConnectedAffineGeometryStatement.{u}`. The
statement module and its imports are unchanged. Both the field and the
universe `u` are arbitrary; the hypotheses are smoothness, affineness and
ordinary `ConnectedSpace` of each actual group scheme.

The first conjunct gives geometric integrality of the group structure
morphism. The second gives affineness, local finite type, quasi-compactness
and geometric integrality of the actual binary product `H₁.X ⊗ H₂.X` in
`Over (Spec k)`. This is the scheme product used by the commutator
construction.

## Implemented proof

The private helper `geometricallyConnected_of_connected_affine` takes a
connected affine group scheme locally of finite type over a field. Its
`GrpObj` structure is passed to the published adapter
`GoodReductionJacobian.relativeGroupLawOfGrpObj`. That adapter constructs
a relative group law on the morphisms from every test scheme, preserving
the actual group multiplication, unit and inverse.

Affineness supplies quasi-compactness. The published theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`
therefore applies. We use precisely its open immersion `i : G₀ ⟶ G`, the
geometric connectedness of `i ≫ f`, and the equality of the image of `i`
with the connected component of the identity. The other conclusions of
that theorem are unnecessary here.

Since `G` is connected, `PreconnectedSpace.connectedComponent_eq_univ`
makes this image all of `G`. The open immersion is consequently an
isomorphism by
`isIso_of_isOpenImmersion_of_opensRange_eq_top`. Geometric connectedness
respects isomorphisms (as a property stable under base change), so
cancelling `i` proves `GeometricallyConnected f`. This obtains geometric
connectedness from the ordinary connectedness premise and the group
structure.

For the first conjunct, smoothness supplies local finite type, and the
helper gives geometric connectedness. The published theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality` then proves geometric
integrality. That theorem checks every field-valued pullback: smoothness
gives local Noetherianity and domain stalks, and geometric connectedness
gives connectedness of the same pullback. The published connected,
locally Noetherian domain-stalk criterion gives its integrality. Its paired
Markdown documents those geometric inputs and their proofs.

For the product, the underlying structure morphism is definitionally

```text
pullback.fst H₁.X.hom H₂.X.hom ≫ H₁.X.hom.
```

The first projection is a base change of `H₂.X.hom`. Smoothness is stable
under base change and composition. Each factor is geometrically connected
by the helper, and `GeometricallyConnected.comp` gives geometric
connectedness of the product; the universal openness required by that
composition theorem follows from smoothness. Applying
`smoothGeometricIntegrality` to the product proves the last component.
Affineness follows from base change and composition of affine morphisms.
Smoothness gives local finite type, and quasi-compactness is stable under
base change and composition here because the two factor morphisms are
affine.

The scoped `backward.isDefEq.respectTransparency.types` option only lets
Lean recognize the scheme morphism properties during instance synthesis.
It supplies no mathematical hypothesis. No perfection, separability,
characteristic, commutativity or prior geometric connectedness hypothesis
is added.

## Provenance and contributions

This is an internal assembly of existing published Library results; no
external Lean source is copied into this file. The identity-component
result and the actual-group-law adapter are imported from the Library's
Anthropic FLT port at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`. Their paired Markdown records
the original modules, proof route, Apache 2.0 attribution and preserved
all-test-scheme group laws. The smooth geometric integrality theorem is
also imported by its published Lean name.

For an original mathematical source supporting the connectedness step,
The Stacks Project, Varieties, Lemma 33.7.14 (Tag
[04KV](https://stacks.math.columbia.edu/tag/04KV)), proves that a connected
scheme over a field with a rational point is geometrically connected.
The group identity is such a point. This is a more general mathematical
justification of that step; the implemented Lean proof uses the published
finite-type group identity-component theorem described above. The retained
HTML snapshot is registered as
`stacks-04kv-rational-point-geometrically-connected-2026-11-03`, SHA-256
`97f43cda9c3fab7afad5272284c17675cf1e440933e0e8667d86bd9fdc183428`,
file `04KV.html`, Lemma 33.7.14 and its proof. The snapshot has no comments,
and there is no project erratum file for that source.

Worker 1370 wrote the assembly proof and its documentation. Worker 1405
located and registered the original Stacks connectedness source and
contributed the source comparison. The mathematical inputs retain their
published authorship in their own paired documentation.
