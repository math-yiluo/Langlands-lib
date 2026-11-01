# The canonical cubic bundle of ordinary polarized finite-level data

This module constructs actual line bundles and a direct-image module from the
published `Datum P S g d n`, preserving its per-datum dual witnesses and all its
original hypotheses.

For the underlying abelian scheme `A`, polarization parameter map `lambda`,
and Poincaré family `P_A`, `Datum.canonicalBundle` is the published
`poincareDiagonalBundle A _ lambda`. The Library puts the parameter factor
first: this pulls `P_A` back along `lambda` in the first factor and then along
the diagonal of `A`. It is the bundle denoted `L^Delta(lambda)` in Mumford,
Fogarty and Kirwan, *Geometric Invariant Theory*, third edition (1994),
Definition 7.5, printed page 130 / PDF page 143. The source is registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.

`Datum.cubicBundle` is its actual third tensor power, equipped with the local
rank-one property proved by `tensorPow_isLocallyFreeRankOne`.
`Datum.rigidificationModule` is the actual module sheaf
`a.abelian.X.hom_* (a.cubicBundle.obj)`. This module does not assert that the
direct image is locally free, has rank `6^g*d`, or commutes with base change.
Those further results in Definition 7.5 use the separate cohomological
theorems of GIT Proposition 6.13 and remain prerequisites for linear
rigidification.

The general auxiliary construction `poincareDiagonalBaseChangeIso` identifies
the diagonal bundle for the canonical changed parameter map with the actual
pullback of the original diagonal bundle. It assumes just the published
`PicardZeroUniversalBaseChangeStatement` and the displayed abelian scheme,
dual witness and parameter map; the map need not be a polarization. The proof
combines successive line-bundle pullbacks, applies the published
`baseChangePoincarePullbackIso`, and verifies its two projection equations.
The parameter projection uses `dualBaseChangeMap_left_inv_fst`; the other
projection is the pullback diagonal identity.

`Datum.canonicalBundlePullbackIso` applies this construction to the datum's
actual restriction operation. The published
`DualWitness.parameterMap_pullbackMap` equates its polarization parameter map
with the canonical changed map. `Datum.cubicBundlePullbackIso` takes the third
tensor power of that isomorphism and composes with the published actual
pullback/tensor-power comparison. These are isomorphisms of actual line
bundles along every base morphism, with no flatness restriction.

The definitions follow GIT Definition 7.5; the comparison proof is an internal
derivation from the published Poincaré base-change and tensor comparisons. The
module supplies the line-bundle base-change step written there, with no claim
of a direct-image comparison, projective-bundle construction, moduli
representation or ordinary geometric existence theorem.
