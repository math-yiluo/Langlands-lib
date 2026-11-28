# The regular-patch comparison from the standard family comparison

Module `Langlands.Global.AdelicEisensteinRegularComparisonPassage` proves
`eisensteinRegularComparisonPassage : EisensteinRegularComparisonPassageStatement.{u}`
(statement module `Langlands.Global.AdelicEisensteinRegularComparisonPassageStatement`): given
`BruhatTitsAvailabilityStatement`, `StandardEisensteinFamilyComparisonStatement` and
`RootPresentationRegularityComparisonStatement`, the proposition
`EisensteinFunctionalEquationRegularComparisonStatement` holds. It also proves three auxiliary
results. It uses `AdelicGroupPoints.IsIwasawaCompact.of_range_le` (module
`Langlands.Global.AdelicGoodPositionIwasawaCompactProof`): if `K` has Iwasawa coverage for `p`
and the image of `p` is contained in that of `p'`, then `K` has Iwasawa coverage for `p'`.

## Auxiliary results

- `AdelicGroupPoints.IsIwasawaCompact.of_comp_innerIso`: Iwasawa coverage for a rational
  conjugate `p ≫ Int(s)` gives Iwasawa coverage for `p`. The adelic points of `p ≫ Int(s)` are
  those of `p` conjugated by the adelic point of `s` (`affinePointsTarget_innerIso_hom`), and
  `IsIwasawaCompact.of_conjugate_map` applies with the inverse point.
- `StandardParabolicFamily.isIwasawaCompact_of_presentation`: a subgroup with Iwasawa coverage
  for the minimal standard parabolic `P_∅` of a family has Iwasawa coverage for every parabolic
  `q` with a root presentation. By
  `exists_simultaneousStandardConjugate_of_dynamicRealization`, `q` is conjugate by a rational
  point `g` to a parabolic with the image of a standard parabolic `P_J`. Since `∅ ⊆ J`, the image
  of `P_∅` is contained in that of `P_J` (`StandardParabolicFamily.le_iff_range_le`), so
  `of_range_le`, `IsIwasawaCompact.of_range_eq` and `of_comp_innerIso` give the claim.
- `ParabolicRootPresentation.isIso_subgroupMultiplication`: for a parabolic `q` of a connected
  reductive group with a root presentation `r'` and a geometric unipotent radical `iV` with
  `iV ≫ q` a closed immersion, the Levi-first multiplication `M' × V → Q` is an isomorphism. The realization of the presentation
  by a standard cocharacter `ζ` identifies `Q`, `M'` and, by
  `Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer`, `V` with the dynamic
  parabolic, centralizer and unipotent subgroup of `ζ`; `Dynamic.isIso_subgroupMultiplication`
  (module `Langlands.GroupScheme.Rational.LeviMultiplication`) applies.

## The family comparison for arbitrary data

`FamilyRegularComparison.of_standardFamily` proves the family comparison (predicate of module
`Langlands.Global.AdelicEisensteinFamilyRegularComparison`), at all universes, for arbitrary
data of the general statement: parabolics `P`, `Q` with root presentations `r`, `r'`. Besides
the data of the predicate, it assumes the hypotheses that the predicate itself does not
contain: `G` connected reductive (`hG`), `iU` and `iV` geometric unipotent radicals (`hU`,
`hV`), `π'` a Levi retraction of `Q` (`hπ' : l' ≫ π' = 𝟙 M'`), `(w, c)` a Weyl conjugation
(`hw`), `K` a maximal compact subgroup (`hKmax`) with Iwasawa coverage for `P` and `Q`, and
`rho` a closed embedding (`hrho : IsClosedSubgroup rho`). The proof chains the transport
theorems of the other modules:

1. Let `fam = r.standardFamily hG` and `I = r.standardIndex hG` (module
   `Langlands.Global.AdelicEisensteinFamilyStandardSource`).
   `StandardParabolicFamily.exists_goodCompact` gives a maximal compact `K₀` in good position
   for `fam`, using the Bruhat–Tits hypothesis.
2. `K₀` has Iwasawa coverage for `P_I` (`of_range_le` from `P_∅`), for `P` (same image as
   `P_I`) and for `Q` (`isIwasawaCompact_of_presentation`).
3. `exists_archimedeanConjugate_infinite_eq` gives an archimedean point `s` such that
   `C = t⁻¹ K₀ t`, `t = ofInfinite F G s`, is maximal compact with the same infinite projection
   as `K`. `C` has Iwasawa coverage for `P` and `Q` (`IsIwasawaCompact.conjInv`).
4. `FamilyRegularComparison.of_finiteCompactChange` reduces the comparison for `K` to the one
   for `C` (with index universes enlarged), using
   `ParabolicRootPresentation.isIso_subgroupMultiplication` for `Q`.
   `FamilyRegularComparison.of_conjugateCompact` reduces the comparison for `C` to the one for
   `K₀`.
5. `FamilyRegularComparison.exists_standardSource` replaces `P` by `P_I`,
   `FamilyRegularComparison.exists_standardTarget` replaces `Q` by a standard `P_J` (using the
   regularity comparison hypothesis), and
   `FamilyRegularComparison.exists_normalizerRepresentative` replaces the Weyl conjugation by a
   normalizer point `n` matching the simple roots.
6. `FamilyRegularComparison.of_standard` gives the comparison for `(P_I, P_J, n)` and `K₀` from
   the standard family statement.

The relative Weyl group of the torus of `fam` is the relative Weyl group of `r.data.i`; the
finiteness instance of `r` is reused for it, so that all the predicates in the chain have the
same instance arguments.

## Main theorem

`eisensteinRegularComparisonPassage` introduces the data of
`EisensteinFunctionalEquationRegularComparisonStatement` and applies
`FamilyRegularComparison.single` (one inducing form) to
`FamilyRegularComparison.of_standardFamily.{u, 0, 0}`.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, Theorem 2.3(4), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, is stated for standard parabolics,
Weyl elements of a fixed maximal split torus and a maximal compact subgroup in good position.
The proof here reduces the Library's general statement to that setting.
