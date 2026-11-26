# Local finiteness of `Ξ_main` in the Fréchet spaces `𝔉^R_L`

Module `Langlands.Global.AdelicLocalFinitenessProof`.

## Results

- `uniformGrowthLocalFinitenessBoundaryModel : UniformGrowthLocalFinitenessBoundaryModelStatement.{u, u, u}`:
  for every number field `F`, connected reductive `G`, maximal split torus `iT : T → G`, generic
  cocharacter `ν`, group data `(u, t, z)` with `IsLocalFinitenessGroupData`, admissible data `X`
  of `Ξ_main` on an open `W ⊆ ℂⁿ`, open compact level `L` and `s₀ ∈ W`, there are an index `i`
  with `c_i(s₀) ≠ 0`, Hilbert spaces `B`, `C` in the universe of `F`, and a compact boundary model
  `X.BoundaryModel … L i s₀ B C` (module `AdelicLocalFinitenessBoundaryReduction`).
- `uniformGrowthLocalFiniteness : UniformGrowthLocalFinitenessStatement.{u}`: the published
  statement (module `AdelicLocalFinitenessStatement`; Bernstein–Lapid, Theorem 7.2), from the
  first result by `uniformGrowthLocalFiniteness_of_boundaryModel`.

## Proof of the boundary model

The proof applies `StandardParabolicFamily.exists_boundaryModel` (module
`AdelicLocalFinitenessBoundaryModelConstruction`) to the standard parabolic family
`𝓕 = StandardParabolicFamily.ofMaximalSplitTorus hG iT hT ν hν`, whose torus, embedding and
cocharacter are `T`, `iT`, `ν`, and supplies its hypotheses as follows.

1. Finiteness of the simple roots (`finite_simpleRoots`) gives the `Fintype` instance; the rational
   characters of the minimal parabolic `P₀ = Standard.parabolicScheme iT ν ∅` are free of finite
   rank by `ParabolicRootPresentation.rationalCharacters_free_finite` for the root presentation of
   the empty index of `𝓕`.
2. `exists_siegelAlgebraicSetup_of_generic` gives a Siegel algebraic setup `j : T₀ → T`.
3. `adelicCompatibleIwasawaCompactStatement_of_local`, applied to
   `InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement`,
   `FinitePlaceGroupPoints.parabolicIwasawaStatement` and
   `IntegralIwasawaFamily.existenceStatement`, gives a maximal compact Iwasawa subgroup `K` of `P₀`
   (`IsParabolicIwasawaCompact`). `exists_isSiegelCover_of_chamber` (with `centralSplitCompactQuotient`
   and `adelicSiegelChamberReduction`) gives compact factors `C` with compact subgroup `K` and a
   threshold `t₀` with `IsSiegelCover`; `K` is an Iwasawa subgroup (`isIwasawaCompact`).
4. `adelicLocalFinitenessChamberCoordinates` gives the equivalence `d_T` (equal to
   `realCharacterDualMap` of `T → P₀`) and the chamber coordinates `e`, with root coordinates
   `h_α / localFinitenessRootStep iT ν t α` (positive steps), central coordinates detecting the
   image in the real dual of `G`, and unit vectors for the logarithms of `t_α` and `z_j`.
5. `exists_rootTrivialSection` gives a linear section of the restriction to the real dual of `G`
   vanishing on the simple roots, from the root triviality, linear independence and spanning of
   the central points `z_j` in the group data. With `commute_of_rootTrivial` (from
   `positiveTorusSplitComponent`), `exists_siegelRepresentatives` gives a compact `Ω`, `M > 0`,
   `r' ≥ 0` and, for every `x ∈ G(𝔸)`, a rational `q` with `q x` having finite part in `Ω`, height
   at most `M ht(x)^{r'}`, and minimal-parabolic height `d_T h` with `h_α ≥ log t₀` on the simple
   roots. By the root coordinates, `(e(H₀(q x)))_α = h_α / step_α ≥ log t₀ / step_α = θ_α`.
6. `positiveTorusSplitComponent` supplies `PositiveTorusSplitComponentStatement`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234, Theorem 7.2 and its proof in §§7.6–7.7, pp. 219–221 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). The implemented route goes through
the Hilbert Fredholm criterion with a compact boundary operator (module
`AdelicLocalFinitenessBoundaryReduction`).
