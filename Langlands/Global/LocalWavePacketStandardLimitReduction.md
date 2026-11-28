# Lapid's §8 limit for standard parabolic subgroups from Proposition 1 and the main-term limit

Module `Langlands.Global.LocalWavePacketStandardLimitReduction` states one
proposition, `Langlands.Global.TruncatedStandardWavePacketLimitReductionStatement`.
It is the implication

```
LocalTruncatedEisensteinFamilyUniformInnerProductStatement →
WavePacketMainTermLimitStatement →
EisensteinPointwiseContinuationStatement →
EisensteinJointRootHyperplaneStatement →
IntertwiningSquareIntegrableExpansionStatement →
TruncatedStandardWavePacketLimitStatement
```

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (SHA-256
  `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`,
  volume PDF, page = printed page + 9). The working hypothesis in §2, p.312,
  gives root-hyperplane clearing and finite-dimensional intertwining
  expansions. The first paragraph of §8, p.328, applies the Fourier transform
  on `𝔞_G` to the truncated inner product, then applies Proposition 1 to
  pass to (18).
- J. Arthur, *A trace formula for reductive groups II: applications of a
  truncation operator*, Compositio Math. 40 (1980), 87–121, registered as
  `arthur-1980-trace-formula-reductive-groups-II` (SHA-256
  `12f250ae40730909b8cc1e9c0d679840fd0e57676f2772800f8688c125b6440f`,
  PDF page = printed page − 85). The parameter-family bound in §1,
  Lemma 1.4, pp.95–96, underlies the uniform square-integrability clause of
  the Proposition 1 premise.

## The hypotheses and their roles

- `LocalTruncatedEisensteinFamilyUniformInnerProductStatement` (module
  `Langlands.Global.AdelicTruncatedEisensteinUniformAsymptoticsStatement`):
  the compact subgroup `K`, the projection property of the full-quotient
  truncation, Lapid's (2) uniformly in the central parameter, and the joint
  measurability and locally uniform `L²` bound of truncated Eisenstein
  families. The compact subgroup required by
  `TruncatedStandardWavePacketLimitStatement` is this `K`.
- `WavePacketMainTermLimitStatement` (module
  `Langlands.Global.LocalWavePacketMainTermLimitStatement`): the integral (18)
  of the main terms tends to the right side of (4).
- `EisensteinPointwiseContinuationStatement` and
  `EisensteinJointRootHyperplaneStatement` give jointly continuous and
  left `G(F)`-invariant cleared continuations for the individual inducing
  vectors. Multiply these cleared continuations by the entire family
  coefficients and the complementary factors of a common denominator and
  sum. The meromorphic identity principle identifies the sum with the
  corresponding multiple of the supplied family continuation. The open
  comparison tube is obtained by taking the parameter sufficiently far
  into the common positive chamber of the projected coroot inequalities
  and the positive relative root inequalities. The Cauchy integral argument
  of `continuousAt_of_rootHyperplane_cleared` and density off the clearing
  hyperplanes give joint continuity and rational invariance on the
  holomorphy domain of the family. These properties on the compact parameter
  support give continuous wave packets on the rational quotient and
  justify integration over the parameter inside the compact constant-term
  integrals of truncation.
- `IntertwiningSquareIntegrableExpansionStatement`: expansions of
  `M(w, λ) v` in `A^2_S` with coefficients holomorphic near the imaginary
  axis. For each standard `S`, concatenate the finite expansions and
  multiply their coefficients by the entire family coefficients to obtain
  the main-term data of formula (2).

## The argument the implication records

Write `G(F) \ G(𝔸)` as the product of `G(F) \ G(𝔸)¹` and the positive points
of the split centre, parametrized by `y ∈ ℝ^m` through a basis `cd` of `𝔞_G`.
The Eisenstein series transform under the centre by `e^{i⟨z, y⟩}`, where `z`
is the central component of the parameter, and the truncation commutes with
central translations. In coordinates `(u, z)` adapted to the central
parameter, the truncated wave packet at `g s(y)` is a Fourier integral in `z`
of truncated Eisenstein integrals over `u`. The Plancherel formula on `ℝ^m`
and Fubini (justified by the third part of the uniform Proposition 1) give

`(Λ^T Θ, Λ^T Θ') = (2π)^{m − n − n'} ∫ z ∫ u ∫ u' ∑ c_j \bar c'_{j'} (Λ^T E_j, Λ^T E'_{j'})_{G(F) \ G(𝔸)¹}`.

The pairs of parameters have equal central components and range over a
compact set. The denominator factors vanish on hyperplanes of measure zero
in these coordinates, since the projected coroots pair nontrivially with
the noncentral parameters. The uniform error estimate can therefore be
integrated over the common support. Along `T = j v₀` the error tends to zero
exponentially, and `I(T)` of `WavePacketMainTermLimitStatement` tends to the
right side of (4). The Fourier representation gives square integrability of
the truncations. Applying the same calculation to the two diagonal pairs
gives their eventually bounded squared norms.
