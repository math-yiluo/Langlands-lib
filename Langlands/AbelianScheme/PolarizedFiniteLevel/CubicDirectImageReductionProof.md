# Proof of the reduction of the cubic direct-image theorem to fibres

`cubicDirectImageReduction : CubicDirectImageReductionStatement.{u}` proves
that `CubicFibreCohomologyStatement` implies `CubicDirectImageStatement`.

## Chosen geometric fibres

`Datum.cubicBundle_chosenGeometricFibre` assumes `H :
CubicFibreCohomologyStatement`, `0 < d`, a datum `a : Datum P S g d n`, an
algebraically closed field `k` and a morphism `b : Spec k ⟶ S`. It concludes
that the pullback of `a.cubicBundle` along `pullback.fst a.abelian.X.hom b` has
zero `relativeCohomology` along `pullback.snd a.abelian.X.hom b` in every
positive degree, and degree-zero cohomology of `k`-dimension `6^g*d`.

Proof. The published pullback datum `a.pullback b` lies over `Spec k`, and its
structure morphism `(a.pullback b).abelian.X.hom` is the chosen projection
`pullback.snd a.abelian.X.hom b`. Applying `H` to `a.pullback b` gives the
vanishing and the dimension for `(a.pullback b).cubicBundle`. The published
canonical isomorphism `a.cubicBundlePullbackIso b` identifies this bundle with
the pullback of `a.cubicBundle`; applying `relativeCohomology` to its inverse
transports both conclusions.

## The reduction

Given `H`, a locally noetherian `S` (the hypothesis is not used), `0 < d` and a
datum `a`, the structure morphism `a.abelian.X.hom` is smooth and proper, since
`a.abelian` is an abelian scheme. The theorem
`pushforward_isLocallyFreeOfRank_and_isIso_of_geometricFibres` of
`Langlands.AlgebraicGeometry.Modules.GeometricFibreDirectImage`, applied to
`a.abelian.X.hom`, `a.cubicBundle` and `r = 6^g*d` with the fibre hypothesis
above, gives:

1. `(Scheme.Modules.pushforward a.abelian.X.hom).obj a.cubicBundle.obj`, which
   is `a.rigidificationModule`, is locally free of rank `6^g*d`;
2. for every `b : S' ⟶ S`, the canonical map
   `pushforwardBaseChange b a.abelian.X.hom (a.pullback b).abelian.X.hom
   (pullback.fst a.abelian.X.hom b) _ a.cubicBundle.obj` is an isomorphism; it
   is applied to the chosen pullback square `IsPullback.of_hasPullback`.

The first item is the rank conclusion. By definition,
`a.rigidificationBaseChangeMap b` is the composite of the map in item 2 with
the pushforward of the inverse of `a.cubicBundlePullbackIso b`. The latter is
the `hom` of the isomorphism `(Scheme.Modules.pushforward _).mapIso (...).symm`,
so the composite is an isomorphism by `IsIso.comp_isIso'`.

## Dependencies

- `Langlands.AlgebraicGeometry.Modules.GeometricFibreDirectImage` (new helper
  module in this contribution), which uses the published
  `sections_of_geometricFibreCohomologyDegreeZero`,
  `pushforward_isLocallyFreeOfRank_and_isIso_pushforwardBaseChange` and
  `relativeCohomologyPullbackIso`;
- the published `Datum.pullback`, `Datum.cubicBundle`,
  `Datum.cubicBundlePullbackIso` and `Datum.rigidificationBaseChangeMap`.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
