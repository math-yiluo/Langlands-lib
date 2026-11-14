# Draft: `N(K)`-stability of the torus filtration over `K = F^ur` (clause 3 of KP Lemma 7.2.3)

Author: Worker 119 (Task 5552), proof material for S1 (Task 5890) of Task 5647's
decomposition. This is an unreviewed draft. It compiles against Library commit `24789a71`
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (diagnostic `81100a84`). It uses only
the standard axioms, and its theorems assume no unproved statement.

Lean module (draft): `Langlands.Geometry.Building.KPLocalCentralizerFiltrationNormalizerStable`.

## Setting and binder convention

- `F : Type u` is a nonarchimedean local field of any characteristic, `K = UnramifiedClosure F`,
  `H` an affine group scheme over `Spec K`, and `B : MaximalUnramified.BuildingData F H`.
- The first part of the file works with any presentation of `Z` by a torus:
  `T : CommGroupScheme (Spec K)` with `[IsAffine T.X.left]`, `hT : IsTorus T.toGrp`, and
  `e : T.toGrp ≅ B.centralizer.Z`.
- `localCentralizerFiltration B T hT e r` is `Z(K)_r`, the image of the published
  `localTorusFiltration F T hT r` under `rationalPoints.map e.hom`.
  `localCentralizerFiltrationImage B T hT e r` is its image `j(Z(K)_r)` in `H(K)` under
  `B.centralizer.j`.
- The last section uses D1's convention (Task 5875, Library module `KPLocalMoyPrasadGroups`):
  the single binder `hZ : IsTorus B.centralizer.Z`, with `Z(K)_r = B.centralizerTorusFiltration hZ r`
  and `j(Z(K)_r) = B.centralizerTorusImage hZ r`. It takes `T = B.centralizerTorus hZ` and
  `e = Iso.refl _`.

## Declarations

- `centralizerConjIso B n`: conjugation by `n ∈ N(K) = normalizerPoints B.i`, restricted to
  `Z = B.centralizer.Z`, as an automorphism of the group scheme `Z`. It is the `K`-level copy
  of the Library's `ParahoricBuildingData.centralizerConjIso`. It is built with
  `SubgroupFunctor.IsRepresentedBy.isoOfComap` from the inner automorphism `H.innerIso n` and
  `torusCentralizer_comap_innerIso_normalizer`: conjugation by a normalizer point preserves
  the centralizer subgroup functor that `B.centralizer.j` represents.
- `map_centralizerConjIso`: on `K`-points, `j(c_n(z)) = n · j(z) · n⁻¹`.
- `torusConj B T e n : T ⟶ T`: the same automorphism transported to `T` along `e`, as a
  morphism of commutative group schemes.
- `map_localCentralizerFiltration_conj_le`: `c_n` maps `Z(K)_r` into itself. This is the
  published functoriality `map_localTorusFiltration_le` applied to `torusConj B T e n`.
- `map_conj_localCentralizerFiltrationImage_le`: conjugation by `n` maps `j(Z(K)_r)` into
  itself, by the previous two results.
- `localCentralizerFiltration_isNormalizerStable`: clause 3 of S1 in the form of
  `ParahoricBuildingData.CentralizerFiltration.IsNormalizerStable`: for every
  `n ∈ normalizerPoints B.i` and `r : ℝ≥0`, the image of `j(Z(K)_r)` under `MulAut.conj n` is
  `j(Z(K)_r)`. The inclusion `⊆` is the previous result. The inclusion `⊇` applies the
  previous result to `n⁻¹` and then conjugates by `n`.

In namespace `Langlands.Geometry.Building.MaximalUnramified.BuildingData` (D1's convention):

- `centralizerTorusFiltration_eq_localCentralizerFiltration` and
  `centralizerTorusImage_eq_localCentralizerFiltrationImage`: D1's `Z(K)_r` and `j(Z(K)_r)`
  equal `localCentralizerFiltration` and `localCentralizerFiltrationImage` for
  `T = B.centralizerTorus hZ` and `e = Iso.refl _`. These are D1's transport lemmas
  `centralizerTorusFiltration_eq_map_iso` and `centralizerTorusImage_eq_map_iso` at that
  presentation.
- `centralizerTorusImage_isNormalizerStable`: clause 3 of S1 for D1's filtration. For every
  `n ∈ normalizerPoints B.i` and `r : ℝ≥0`, the image of `B.centralizerTorusImage hZ r` under
  `MulAut.conj n` is `B.centralizerTorusImage hZ r`. Proof: rewrite with the second
  identification and apply `localCentralizerFiltration_isNormalizerStable`.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §7.2, Definition 7.2.1 and
Lemma 7.2.3 (printed p.245–246). The `N(K)`-stability is the part of Lemma 7.2.3 that needs
only the functoriality of the torus filtration (KP Definition 7.2.2). In the Library that
functoriality is `map_localTorusFiltration_le`.

## Status of the other clauses of S1

Clause 1 (commutator friendliness) is derived in the draft module
`KPLocalCentralizerFiltrationCommutatorFriendly` from `KPLocalCorootComponentStatement`
(Task 5911, KP Proposition 7.1.1 over `K`). Clause 2 (root compatibility) is derived in
`KPLocalCentralizerFiltrationRootCompatible`: depth `0` is proved outright, and positive
depth follows from `KPLocalTorusRootCommutatorStatement` (Task 5918). Both statements are
published in the Library but not yet proved; their proofs are Task 6192 and Task 6194.
