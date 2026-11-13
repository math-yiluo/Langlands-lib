# Springer's split fundamental set

Author: Worker 2.

This module removes the Iwasawa premise from the split fundamental-set
reduction of `AdelicSplitFundamentalSetFromRankOne`, and then proves
Springer's split fundamental-set theorem. Its two final theorems are

```lean
theorem splitAdelicFundamentalSet_of_splitRankOne
    (hsplit : SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u}) :
    SplitAdelicFundamentalSetStatement.{u}

theorem splitAdelicFundamentalSet : SplitAdelicFundamentalSetStatement.{u}
```

The first shows that the split rank-one height bound is the only input
needed for Springer's split fundamental-set theorem. Neither
`AdelicGroupPoints.ParabolicIwasawaStatement` nor
`FinitePlaceGroupPoints.ParabolicIwasawaStatement` is assumed. The second
supplies that input from the published theorem
`RepresentationGrowth.splitRankOneParabolicRationalOrbitHeightBound`
(module `SplitRankOneAdelic`), so it proves the published statement
`SplitAdelicFundamentalSetStatement` (module `AdelicSplitFundamentalSet`)
with no hypotheses.

## Why a compact set suffices

The published chamber argument (`hasWeakChamberReduction_of_rootLeviHeightBounds`
in `AdelicSplitChamberReduction`) takes a compact subgroup `K` with
`P_∅(𝔸) · K = G(𝔸)`. It uses this `K` in only three ways:

1. every norm-one `g` factors as `p · k` with `p ∈ P_∅(𝔸)` and `k ∈ K`;
2. `k` lies in `G(𝔸)¹`, so `p` does too, and the minimal-parabolic norm factors
   apply to `p`;
3. the height-minimum transport is applied to `k⁻¹`, for a compact set of
   such elements.

The subgroup property enters only through `compactSubgroup_le_normOneSubgroup`
in step 2 and through `k⁻¹ ∈ K` in step 3. A compact set `Ω ⊆ G(𝔸)¹` with
`P_∅(𝔸) · Ω = G(𝔸)` serves equally well, using the compact set `Ω⁻¹` in
step 3. The published
`AdelicSiegelFactors.IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover`
(module `AdelicParabolicCompactCover`) supplies such an `Ω` unconditionally for
every Siegel setup.

## Results

All results are in `Langlands.Global.AdelicSiegelFactors`, for actual data
`F G T i ν T₀ j` with `[IsAffineHom G.X.hom]`. The factorization and
fundamental-set theorems below, from
`exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover` on, assume
an actual setup `IsSiegelAlgebraicSetup F G T i ν T₀ j`.

- `HasMinimalParabolicNormFactors.exists_cover_factors` is the set version of
  `HasMinimalParabolicNormFactors.exists_iwasawa_factors`. Let
  `Ω ⊆ normOneSubgroup F G` satisfy
  `Set.range (map F _ G (Standard.parabolicHom i ν ∅)) * Ω = Set.univ`. Then
  every norm-one `g` equals `n_U(n) · m_L(m) · positiveMap(a) · k` with
  `k ∈ Ω`, a unipotent point `n`, a norm-one minimal-Levi point `m` and an
  intrinsic positive point `a` of `T₀`.
- `HasWeakChamberCoverReduction F G T i ν T₀ j Ω` (a `Prop`-valued
  definition) is the set version of the published
  `HasWeakChamberReduction F G T i ν T₀ j K`. Its body is the same, except that
  the compact factor `k` ranges over a set `Ω` of adelic points instead of a
  subgroup `K`: some `t : ℝ≥0ˣ` makes every norm-one `g` satisfy
  `n_U(n) · m_L(m) · positiveMap(a) · k = rational(q) · g` with a rational `q`,
  a unipotent point `n`, a norm-one minimal-Levi point `m`, a positive point `a`
  in `weakSimpleRootChamber … t`, and `k ∈ Ω`. No compactness of `Ω` is part
  of the definition.
- `HasWeakChamberReduction.hasWeakChamberCoverReduction`: a reduction for a
  subgroup `K` is one for the set `(K : Set _)`.
- `exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover`: assume
  `[LocallyOfFiniteType G.X.hom]`, connected reductivity,
  `HasRootLeviHeightBounds F G T i ν`, and a compact `Ω` as in
  `exists_cover_factors`. Then some
  `t : ℝ≥0ˣ` has the following property. Every norm-one `g` admits a rational
  `q`, factors `n, m, a` with `a` in `weakSimpleRootChamber … t`, and `k ∈ Ω`
  with `n_U(n) · m_L(m) · positiveMap(a) · k = rational(q) · g`. This is the
  conclusion of `HasWeakChamberReduction` with `k ∈ Ω` in place of `k ∈ K`.
  `hasWeakChamberCoverReduction_of_rootLeviHeightBounds` states the same
  conclusion as `HasWeakChamberCoverReduction F G T i ν T₀ j Ω`.
- `hasRightAdelicFundamentalSet_of_rootLeviHeightBounds_of_cover`: under the
  same hypotheses, `HasRightAdelicFundamentalSet F G T i ν` holds.
- `hasRightAdelicFundamentalSet_of_rootLeviHeightBounds`: the same conclusion
  without the cover hypothesis, which is now supplied by
  `hasCompactNormOneParabolicCover`.
- `splitAdelicFundamentalSet_of_splitRankOne` and `splitAdelicFundamentalSet`,
  displayed above.

## Proofs

`exists_cover_factors` is the proof of `exists_iwasawa_factors`, except that
`k ∈ G(𝔸)¹` comes from `Ω ⊆ normOneSubgroup F G` rather than from
compactness of a subgroup.

`exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover` repeats the
proof of `hasWeakChamberReduction_of_rootLeviHeightBounds` with three changes.
The compact set given to `exists_pos_chainHeightMinimalSet_compact_transport`
is `Ω⁻¹`, compact because inversion is continuous. The Iwasawa factorization
is `exists_cover_factors`. The norm-one memberships of `k` and `k⁻¹` come from
`Ω ⊆ normOneSubgroup F G`, and `k⁻¹ ∈ Ω⁻¹` replaces `K.inv_mem`. The finite
enumeration of simple roots, the adapted prefix minima, the root-Levi bounds
and the commutation of the torus with the minimal Levi are unchanged.

`HasWeakChamberReduction.hasWeakChamberCoverReduction` and
`hasWeakChamberCoverReduction_of_rootLeviHeightBounds` hold by definitional
unfolding: membership in `(K : Set _)` is membership in `K`, and the
definition's body is the conclusion of the factorization theorem.

`hasRightAdelicFundamentalSet_of_rootLeviHeightBounds_of_cover` is the
inversion of `HasWeakChamberReduction.hasRightAdelicFundamentalSet`. Apply the
factorization to `g⁻¹` and invert. The compact factor is `k⁻¹ ∈ Ω⁻¹`, so the
compact set of the fundamental set is the set of norm-one points lying in
`Ω⁻¹`. This set is compact because `Ω⁻¹` is compact and contained in
`G(𝔸)¹`. The torus factor is the inverse of the positive point, with
simple-root norms at most `t⁻¹`. The parabolic factor is the inverted
Levi–unipotent product, which lies in the norm-one subgroup of `P_∅` for all
characters of `P_∅`.

`splitAdelicFundamentalSet_of_splitRankOne` feeds the published
`hasRootLeviHeightBounds_of_splitRankOne` into the previous theorem. That
theorem uses the maximal-torus hypothesis of the split statement.

`splitAdelicFundamentalSet` is `splitAdelicFundamentalSet_of_splitRankOne`
applied to Worker 10's published
`RepresentationGrowth.splitRankOneParabolicRationalOrbitHeightBound`.

## Provenance and scope

This is a derived adapter. `HasWeakChamberCoverReduction` is an internal
definition, copied from the published `HasWeakChamberReduction` (module
`AdelicEmptyRootChamberReduction`) with a set in place of a subgroup. Springer, *Reduction theory over global fields*
(1994), §2.1, printed p.211 (PDF p.5), defines Siegel sets as `K · S(c) · P(A)¹`
with `K` a compact **subset** of `G(A)`. His fundamental-set theorem (F) and
the split case (§§3.2–3.3, printed pp.214–215) need no subgroup property. The
registered source is `springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The chamber proof reused here is Worker 5253's
`AdelicSplitChamberReduction`, itself a fixed-setup version of the published
`AdelicChamberFromRankOneHeight`.

This module does not prove the split rank-one height bound. The conditional
theorem keeps it as an explicit hypothesis, and the unconditional theorem
imports the published proof from `SplitRankOneAdelic`.
