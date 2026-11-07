# Finite-level approximation on `L²([G])` and its a.e. cuspidal subspace

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.QuotientFullAEL2FiniteApproximationStatement`
is a proposition about `L²` of the restriction split-centre quotient
`RestrictionSplitCentre.Quotient F G S j` and its published almost-everywhere
cuspidal subspace. This quotient has the shape `[G] = A_G G(F) \ G(A_F)` of
Getz--Hahn (2.20)--(2.21) (`getz-hahn-2024-automorphic-representations`,
printed pp. 68--69). The subspace follows their (6.20)--(6.21) (printed
p. 168). The proposition is the `[G]` counterpart of the published
positive-torus
`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2FiniteApproximationStatement`.
Its conclusion contains that of
`QuotientL2FiniteApproximationStatement` (module
`GroupSchemeRestrictionQuotientL2FiniteApproximationStatement`, not imported
here) and adds the cuspidal subspace, with one sequence of subgroups for both
spaces.

## Hypotheses

The proposition quantifies over:

- a number field `F : Type`, and a group scheme `G` over `Spec F` whose
  underlying scheme is affine and locally of finite type, with
  `hG : IsConnectedReductive G` and `hPD : ParabolicDynamicStatement.{0}`.
  `hPD` is the structural hypothesis taken by the published cuspidal subspace;
- a commutative group scheme `S` over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`;
- a commutative group scheme `T` over `F` and `i : T.toGrp ⟶ G` with
  `h : subgroup F G S j = imageSubgroup F T G i`, injective
  `characterRestrict i` (`hi`) with finite-index range, `hc : IsCentral i`
  and `hT : IsSplitTorus T.toGrp`;
- right invariance of Haar measure on `normOneSubgroup F G` (an instance
  argument), and any proof `hInv'` of
  `QuotientRightInvariant F G (quotientHaarMeasure F G S j)`.

These are the hypotheses of the published finite averages on `L²([G])` and
on the cuspidal subspace, which the conclusion uses. They are a sufficient
setting; the proposition does not claim that they are needed.

## Conclusion

Write `Sq` for the published `quotientFullAEL2CuspidalSubmodule F G hPD hG h
hi hc hT` of `L²([G]) = Lp ℂ 2 (quotientHaarMeasure F G S j)`. Write `ρA` for
the published finite right action `rationalQuotientL2FiniteRightAction` on
`L²([G])` and `ρB` for the published finite cuspidal action
`quotientFullAEL2CuspidalFiniteRightAction` on `Sq`. Write `P` for the
published orthogonal projection `quotientFullAEL2CuspidalOrthogonalProjection`
from `L²([G])` onto `Sq`, and `Q` for the published ambient projection
`quotientFullAEL2CuspidalAmbientProjection`, with codomain `L²([G])`.

The proposition asserts that there are a sequence
`K : ℕ → OpenSubgroup (FiniteAdelicGroupPoints F G)` and a proof `hK` that
every `K n` is compact as a subset of the finite adelic points, such that the
sets `K n` form an antitone basis of the neighborhood filter of `1`, and the
following hold. Let `A n` be the published average
`rationalQuotientL2FiniteAverage` over `K n` on `L²([G])`, and `B n` the
published average `quotientFullAEL2CuspidalFiniteAverage` over `K n` on `Sq`.
Both use `CompactSpace (K n)` obtained from `hK n`.

- `A n φ` lies in `Langlands.fixedVectors ρA (K n).toSubgroup` for every `n`
  and `φ`, `A n φ` tends to `φ` for every `φ`, and the
  `Langlands.IsSmoothVector` vectors of `ρA` are dense in `L²([G])`.
- `B n ψ` lies in `Langlands.fixedVectors ρB (K n).toSubgroup` for every `n`
  and `ψ`, `B n ψ` tends to `ψ` in `Sq` for every `ψ`, and the
  `Langlands.IsSmoothVector` vectors of `ρB` are dense in `Sq`.
- `(B n ψ).val = A n ψ.val` for every `n` and `ψ : Sq`.
- `P (A n φ) = B n (P φ)` and `Q (A n φ) = A n (Q φ)` for every `n` and `φ`.

The sequence is chosen before any vector is quantified. There is no separate
sequence for the cuspidal subspace and no other approximation operator.

## Provenance and scope

The quotient `[G]` is Getz--Hahn (2.20)--(2.21) and the cuspidal subspace their
(6.20)--(6.21). The proposition is the `[G]` form of the published internal
positive-torus statement, with the same conclusion for the published `[G]`
actions, averages and projections. No theorem of Getz--Hahn is cited for it.
The module states the proposition and contains no proof. The intended proof
takes the sequence and the ambient conclusions from
`QuotientL2FiniteApproximationStatement`. It moves convergence to `Sq` through
the published identity `quotientFullAEL2CuspidalFiniteAverage_val`, and takes
the projection identities from the published
`quotientFullAEL2CuspidalOrthogonalProjection_finiteAverage` and
`quotientFullAEL2CuspidalAmbientProjection_finiteAverage`.

The density concerns the finite adelic actions only. The proposition supplies
no archimedean smoothness, admissibility, finite volume, existence of nonzero
cusp forms or spectral decomposition. It does not prove
`ParabolicDynamicStatement`, existence of `T` and `i`, or injectivity and
finite index of `characterRestrict i`.
