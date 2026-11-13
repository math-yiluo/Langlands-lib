# Proof of the cubic direct-image theorem

`cubicDirectImage : CubicDirectImageStatement.{u}` proves the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageStatement`. Let
`S` be a locally noetherian scheme, `0 < d`, and `a : Datum P S g d n`. Then
`a.rigidificationModule`, the direct image of the cubic diagonal bundle
`a.cubicBundle` along the abelian scheme's structure morphism, is locally free
of rank `6^g*d`. Moreover, for every morphism `b : S' ⟶ S`, the canonical
comparison `a.rigidificationBaseChangeMap b` is an isomorphism.

## Proof

The proof applies two published theorems:

- `cubicDirectImageReduction : CubicDirectImageReductionStatement.{u}`
  (`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageReductionProof`).
  It proves the implication `CubicFibreCohomologyStatement →
  CubicDirectImageStatement` by cohomology and base change. Pulling the datum
  back to a geometric fibre `Spec k ⟶ S`, with `k` algebraically closed, and
  transporting along the canonical isomorphism `a.cubicBundlePullbackIso`
  turns the fibre statement into vanishing of higher cohomology and a degree-0
  dimension of `6^g*d` on every chosen geometric fibre. The helper
  `pushforward_isLocallyFreeOfRank_and_isIso_of_geometricFibres`
  (`Langlands.AlgebraicGeometry.Modules.GeometricFibreDirectImage`) then gives
  the rank and the invertibility of the base-change map for the smooth proper
  structure morphism.
- `cubicFibreCohomology : CubicFibreCohomologyStatement.{u}`
  (`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyProof`).
  Over an algebraically closed field, the cubic diagonal bundle of a datum has
  no cohomology in positive degrees, and its global sections have dimension
  `6^g*d`.

The theorem is `cubicDirectImageReduction cubicFibreCohomology`.

## Axioms

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
