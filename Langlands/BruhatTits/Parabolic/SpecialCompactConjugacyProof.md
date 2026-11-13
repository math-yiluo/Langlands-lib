# Parabolic conjugacy under a subgroup satisfying Iwasawa factorization

Author: Worker 283.

The theorem `Langlands.BruhatTits.specialCompactParabolicConjugacy` proves exactly
`Langlands.BruhatTits.SpecialCompactParabolicConjugacyStatement`, with its universe
parameter and hypotheses unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 edition, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.5.1, first assertion of the Corollary, printed p.123 / PDF p.129. The
published statement isolates the algebraic consequence of property (1) of the
preceding Theorem, so it applies over any field and to any subgroup satisfying
that factorization.

The implemented proof uses the published `standardParabolicClassification` to
choose a set `J` of simple relative roots and a rational point `g` such that
`P(zeta) = (P_J).comap (G.innerIso g).hom`. The published
`standardParabolicOrder` gives `P_empty ≤ P_J` from `empty ⊆ J`.
The first equality in `Iwasawa.PointProductEqualities` factors `g = p * k`
with `p ∈ P_empty(F)` and `k ∈ K`.

Membership of `p` in `P_J(F)` follows by evaluating the subgroup-functor
inclusion at the base test scheme. The published
`SubgroupFunctor.comap_innerIso_hom_eq_of_mem` then identifies
`(P_J).comap (G.innerIso p).hom` with `P_J` on every test scheme: a subgroup
contains the constant restriction of each of its base points, and is stable
under conjugation by such a point. Finally `innerIso_mul_hom` and
`SubgroupFunctor.comap_comp` rewrite the pullback for `p * k` as the successive
pullbacks for `p` and `k`, and the first one cancels. This gives
`P(zeta) = (P_J).comap (G.innerIso k).hom`, the required orientation
`k⁻¹ P_J k`.

Only the `P_empty(F) K` factorization is used; the theorem retains the full
published two-sided premise. The proof establishes equality of subgroup
functors on all test schemes directly.

The module imports the unchanged target statement, the published classification
and order proofs, and `StandardLeviLiftIndependence` for the general
subgroup-functor conjugation identity. It adds no definitions or hypotheses.
