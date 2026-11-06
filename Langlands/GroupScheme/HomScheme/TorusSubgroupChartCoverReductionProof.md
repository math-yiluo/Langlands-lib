# Reduction of chart covers to bases of finite type over `ℤ`

Worker 1412. This module proves the target
`TorusSubgroupModuli.ChartCoverReductionStatement.{u}` from
`Langlands.GroupScheme.HomScheme.TorusSubgroupChartStatements`, uniformly in the
universe `u`. The statement is the noetherian reduction in SGA 3, Exposé XI,
proof of Theorem 4.1, registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF page 21. There
one reduces to `S = Spec A`, writes `A` as a filtered union of subrings of
finite type over `ℤ` and descends `G` (EGA IV 8). The Lean proof follows this
route, using `TorusSubgroupModuli.HasChartCover` from
`Langlands.GroupScheme.HomScheme.ChartCoverTransport` as its chart-cover
property. By definition, `HasChartCover G` is the conclusion of
`ChartCoverStatement` for `G`, and `FiniteTypeChartCoverStatement` asserts it
for every smooth affine group scheme over `Spec R` with `R` of finite type over
`ℤ`.

## Affine bases

`hasChartCover_affine` assumes `FiniteTypeChartCoverStatement.{u}`. It shows
that every actual group scheme `G` over `Spec R`, for any `R : CommRingCat.{u}`
and with `G.X.hom` smooth and affine, has a chart cover. The steps are:

1. `exists_finiteType_model`, from
   `Langlands.GroupScheme.HomScheme.SmoothAffineGroupFiniteTypeModel`, gives a
   ring `R₀ : Type u` of finite type over `ℤ` and a ring map `φ : R₀ → R`. It
   also gives a smooth affine group scheme `G₀` over `Spec R₀` and an
   isomorphism `e : G ≅ (G₀)_{Spec R}`.
2. The hypothesis gives a chart cover of `G₀`.
3. `hasChartCover_baseChange`, from
   `Langlands.GroupScheme.HomScheme.ChartCoverBaseChange` (Worker 706), carries
   it to a chart cover of `(G₀)_{Spec R}`.
4. `hasChartCover_iso` with `e.symm` carries that to a chart cover of `G`.

## Arbitrary bases

`chartCoverReduction : ChartCoverReductionStatement.{u}` fixes an arbitrary
scheme `S : Scheme.{u}` and an actual group scheme `G` over `S` with `G.X.hom`
smooth and affine. It applies `hasChartCover_of_openCover` from
`Langlands.GroupScheme.HomScheme.ChartCoverOpenExtension` to the family of all
affine opens `V` of `S`, through the open immersions
`IsAffineOpen.fromSpec : Spec Γ(S, V) → S`:

- The family covers `S`: affine opens form a basis
  (`Scheme.isBasis_affineOpens`), so every point lies in some affine open `V`.
  The range of `fromSpec` is `V` (`IsAffineOpen.range_fromSpec`).
- Each restriction `G_{Spec Γ(S, V)}` is the base change along `fromSpec`, so its
  structure morphism is a pullback of `G.X.hom`. It is therefore smooth and
  affine, and `hasChartCover_affine` gives it a chart cover.

The resulting chart families are actual families over the original base `S`.
They satisfy the published `IsOpenChart` and `CoversFieldPoints` exactly as
defined. Nothing is assumed about `S` (it need not be noetherian, affine or
quasi-compact) and no moduli scheme is assumed.
