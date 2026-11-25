# Group properties of the K-level Moy–Prasad groups

The theorem
`Langlands.Geometry.Building.MaximalUnramified.localMoyPrasadGroupProperties`
in `Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesProof` proves exactly
`MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement.{u}` at arbitrary
universe `u`.

It retains the published setting: a nonarchimedean local field `F` of any
characteristic, `K = UnramifiedClosure F`, an affine group scheme `H` over
`Spec K`, supplied `B : MaximalUnramified.BuildingData F H`, and
`hZ : IsTorus B.centralizer.Z`. The groups are the actual
`B.moyPrasad hZ x r` of `KPLocalMoyPrasadGroups`, with torus filtration `B.centralizerTorusFiltration hZ r`
and its image `B.centralizerTorusImage hZ r`. The target statement, those
definitions, and their hypotheses are unchanged.

## Published inputs and assembly

The proof applies
`localMoyPrasadGroupProperties_of_torus_filtration` from the companion module
`KPLocalMoyPrasadGroupPropertiesReduction` to the published theorem
`Langlands.Geometry.Building.quasiSplitLocalTorusFiltration` from
`KPQuasiSplitLocalTorusFiltrationProof`. This supplies the three clauses of
`QuasiSplitLocalTorusFiltrationStatement`.
In particular, ordinary torus commutator friendliness and torus/root
compatibility have proofs rather than remaining as additional premises.

The reduction discharges the other global inputs as follows:

- `MaximalUnramified.localMoyPrasadPositiveProduct` from
  `KPLocalMoyPrasadPositiveProductProof` gives the positive-depth sign product
  cover when applied to ordinary torus commutator friendliness.
- `MaximalUnramified.localMoyPrasadDepthZero` from
  `KPLocalMoyPrasadDepthZeroProof` gives the positive-root intersection equality
  and the pairing-Levi intersection containment at depth zero.
- `Langlands.Geometry.Building.kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates`
  from `RankOneDoubledInputCoroot`, applied to the published
  `Langlands.Geometry.Building.quasiSplitValuedRankOneCoordinates` from
  `QuasiSplitValuedRankOneCoordinatesProof`, gives the sharper centralizer
  estimate at depth `2d` whenever either opposite-root input lies in its
  doubled-root group. This estimate uses the actual torus filtration.

These inputs have no conclusion of `LocalMoyPrasadGroupPropertiesStatement` as a premise. In particular, the doubled-root
estimate is supplied independently of normality, factorization and intersection.
The final theorem has no argument for an unproved proposition, apartment axiom
or extra filtration property.

## Implemented proof of the eight clauses

The fixed-building assembly
`BuildingData.localMoyPrasadGroupProperties_of_estimates` specializes these
inputs at `F`, `H`, `B` and `hZ` and combines the following conclusions.

1. **Normality.**
   `BuildingData.localMoyPrasadNormality_of_torus_commutator_bounds` in
   `KPLocalMoyPrasadDoubleRootConjugation` proves that `G_{x,0}` normalizes
   `G_{x,r}`. It reduces to torus and root generators using the published
   `KPLocalMoyPrasadCovariance`. The companion integer, ordinary-opposite and
   mixed conjugation modules give the root bounds.
   `QuasiSplitLocalTorusFiltrationStatement` and the independent
   doubled-root estimate supply the central coordinates. The root-direction
   classification uses the published integer-valuation affine-root results.
2. **Equivariance.**
   `BuildingData.localMoyPrasadEquivariance_of_torus_commutator_bounds` in the
   same module gives both the normalizer and reduced-building forms.
   `BuildingData.centralizerTorusImage_isNormalizerStable` from the published
   `KPLocalCentralizerFiltrationNormalizerStable` handles torus generators;
   root conjugation gives normalizer covariance. The published covariance
   reduction then uses normality and the actual reduced-building quotient
   relation for the general building form.
3. **Commutators.**
   `BuildingData.localMoyPrasadCommutator_of_torus_commutator_bounds` in
   `KPLocalMoyPrasadCommutator` proves
   `⁅G_{x,r}, G_{x,s}⁆ ≤ G_{x,r+s}`. Depth-zero cases follow from normality.
   For positive depths, the proof treats torus/torus, torus/root and
   root/root generators, translating apartment points for ordinary and
   doubled-opposite roots. V3 handles the nonopposite case. The published
   `commutator_closure_le_of_le_normalizer` passes from generators to groups.
4. **Root intersections.**
   `BuildingData.rootIntersection_of_covers` in
   `KPLocalMoyPrasadIntersectionDepthZero` proves the equality for every closed
   root set in an open half-space and every nonnegative depth. Its
   positive-depth case uses
   `BuildingData.rootIntersection_of_productCover` from
   `KPLocalMoyPrasadIntersectionRoot`, using ordered root coordinates.
   Its depth-zero case uses the published positive-root intersection equality
   and the same root-coordinate restriction.
5. **Iwahori factorization.**
   `BuildingData.iwahoriFactorization_of_productCover` in
   `KPLocalMoyPrasadIntersectionLevi` uses the sign product cover and uniqueness
   of the negative-root/Levi/positive-root product. It proves that each
   specified factor belongs to `G_{x,r}` when `r > 0`, as the target requires.
6. **Levi intersections.**
   `BuildingData.leviIntersection_of_covers` in
   `KPLocalMoyPrasadIntersectionDepthZero` combines the positive-depth product
   argument of `BuildingData.leviIntersection_of_productCover` with the
   published depth-zero containment. The reverse depth-zero inclusion follows
   from the defining torus and zero-pairing root generators.
7. **Centralizer intersections.**
   `BuildingData.centralizerIntersection_of_covers` in the same module combines
   `BuildingData.comap_moyPrasad_eq_of_productCover` at positive depth with the
   depth-zero argument. The latter chooses a generic cocharacter, so its
   zero-pairing root set is empty, and uses injectivity of the actual
   centralizer inclusion on points to recover membership in `Z(K)_0`.
8. **Separation.**
   `BuildingData.separated_of_productCover` in
   `KPLocalMoyPrasadIntersectionLevi`, using the open-cell results of
   `KPLocalMoyPrasadIntersectionCell`, fixes the three product coordinates
   across all positive depths. Separation of the root filtrations and the
   torus filtration makes all three coordinates trivial, giving
   `⨅ r : ℝ≥0, G_{x,r} = ⊥`.

The companion `BuildingData.intersectionClauses_of_statements` in
`KPLocalMoyPrasadIntersectionAssembly` collects clauses 4–8. The reduction
combines them with clauses 1–3 into the exact published conjunction.

## Provenance

This is a composition of Library theorems and the companion proofs.
The source targets are those documented in the unchanged statement pair:
Kaletha–Prasad (2023), Proposition 7.3.17, Remark 7.6.5 and (7.6.2),
Proposition 13.2.5(4), Proposition 7.3.12, Lemma 8.5.19 and Lemma 7.3.16.
The companions document their implemented algebraic routes and their use of
the 2024 corrections. This final composition introduces no further source
claim and does not assert the existence of the supplied building data.
