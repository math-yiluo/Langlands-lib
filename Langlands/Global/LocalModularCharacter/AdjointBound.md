# The modular character of `G(K)` is bounded by the Haar scaling of `Ad`

Module `Langlands.Global.LocalModularCharacter.AdjointBound`.

This is internal infrastructure for the proof of
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. No
literature statement is formalized here. The module combines the identity chart of
`IdentityChart` with the chart estimates of `ChartEstimates` into a bound on the modular
character in terms of the adjoint action.

## Setting

- `F` is a field and `G` is an affine group scheme of finite type over `Spec F`
  (`[IsAffine G.X.left]`, `[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]`).
- `K` is a complete, proper, nontrivially normed field that is an `F`-algebra, in the same
  universe as `F`.
- `G(K)` is `G.affinePoints (CommAlgCat.of F K)`. Its topology and group topology are the local
  instances of `IdentityChart`, which are the Library's evaluation topology and topological-group
  instance. The theorems take as instance arguments that `G(K)` is locally compact, Hausdorff and
  second countable, with a Borel measurable structure.
- `chartLieKernelCommGroup` and `chartLieKernelModule` (from `ChartLie`) are local instances, so
  that `adjoint G K g` is a linear map and `LinearMap.det (adjoint G K g)` makes sense.

## Main theorems

Both theorems assume `hG : Smooth G.X.hom`. They also take `g : G(K)`, `c : ℝ≥0`, and a
hypothesis `hc`: for every `d : ℕ`, every Borel measurable structure on `K^d = Fin d → K`, and
every `K`-linear automorphism `A` of `K^d` with `det A = det (adjoint G K g)`, the additive Haar
character `addEquivAddHaarChar (linearPiContinuousAddEquiv A)` equals `c`.

- `modularCharacter_le_of_adjoint_ultrametric`, with `[IsUltrametricDist K]`, concludes
  `Measure.modularCharacter g ≤ c`.
- `modularCharacter_le_of_adjoint_real`, with `[NormedSpace ℝ K]` and
  `[FiniteDimensional ℝ K]`, concludes the same.

## Proof

`exists_identityChart G hG` gives a dimension `d`, a chart `φ` of `G(K)` at the identity with
`φ 1 = 0`, a strict derivative `L` of the chart group law at `(0, 0)` with `L (0, w) = w`, and
for `g` a continuous linear automorphism `A` of `K^d`. This `A` is the strict derivative at `0`
of the chart expression of conjugation by `g`, and `det A = det (adjoint G K g)`. Put the Borel
structure on `K^d` and rewrite `c` as `addEquivAddHaarChar (linearPiContinuousAddEquiv A)`
using `hc`. Then `modularCharacter_le_of_chart_ultrametric` (respectively
`modularCharacter_le_of_chart_real`) from `ChartEstimates` gives the bound. Its last argument,
that the continuous additive automorphism agrees pointwise with `A`, holds by `rfl`.
