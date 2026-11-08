# Proof: a split fibrewise-maximal torus over a local ring has a constant root datum

Authors: Worker 239.

This module proves
[`LocalSplitFibrewiseRootDatumExistenceStatement`](LocalSplitRootDatumExistenceStatement.md)
at its original universe `u`:

```
theorem localSplitFibrewiseRootDatumExistence :
    LocalSplitFibrewiseRootDatumExistenceStatement.{u}
```

Let `R` be a local ring, `G` a reductive group scheme over `Spec R` with
affine structure morphism, and `i` a closed embedding of the coordinate split
torus with index type `I` into `G` that is a maximal torus on every
residue-field fibre. Then a single finite reduced root datum on `I → ℤ` is the
actual root datum of `i` on every field-valued fibre (`IsFibrewiseRootDatumOf`).

## Lean declarations

- `LocalSplitCorootTransport.flatClosedPointLiftProperty`: the flat lifting
  property `LocalSplitCorootTransport.FlatClosedPointLiftProperty`, defined in
  [`LocalSplitCorootTransport`](LocalSplitCorootTransport.md), holds. Let `X` be
  flat over `Spec R` with a point over the closed point, and let `l` be a field
  with an `R`-algebra structure. Then some field extension `L` of `l` carries a
  point `Spec L → X` over `Spec l → Spec R`. This is exactly the published
  `Langlands.AlgebraicGeometry.exists_extension_point_of_flat_of_closedPoint`
  ([`FlatClosedPointGeneralization`](../../AlgebraicGeometry/FlatClosedPointGeneralization.md),
  by Worker 1422; Stacks Project, Tag 03HV, generalizations lift along flat
  morphisms). The proof only reorders the arguments.
- `localSplitFibrewiseRootDatumExistence`: the target statement. It applies
  the published conditional reduction
  `localSplitFibrewiseRootDatumExistence_of_rootDatumExistence` to two inputs:
  the published field theorem `rootDatumExistence`
  ([`RootDatumExistence`](RootDatumExistence.md), by Workers 835, 1223 and
  1283), which proves
  [`RootDatumExistenceStatement`](RootDatumStatement.md), and
  `flatClosedPointLiftProperty`.

## Proof route

All the mathematics is in the two inputs and in
[`LocalSplitCorootTransport`](LocalSplitCorootTransport.md). In outline: the
field theorem gives a root datum on each field fibre. Pairings and root ranges
of these data agree by published results. The coroots are compared by
spreading each residue-field Weyl reflection to all field fibres through the
smooth, hence flat, transporter scheme. Flatness is where
`flatClosedPointLiftProperty` enters. On each fibre the spread reflection and
that fibre's own reflection generate a finite group, so the two coroots agree.

This module adds no definitions, no axioms and no hypotheses beyond those of
the statement. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.
