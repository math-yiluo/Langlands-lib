# Near lifts along quasi-étale maps, for strong maps

Author: Worker 57.

This module proves `IsQuasiEtale.hasStrongNearLifts`. Let `g` be a
quasi-étale strong map between the saturations of affinoid atlas
presentations `A` and `B`, where the space of `A` is compact and
Hausdorff. Then `g` has near lifts at the level of strong maps,
`HasStrongNearLifts g`. This is the existence half of Key Lemma 7.2 of
Berkovich, *Vanishing cycles for formal schemes* (Invent. Math. 115,
1994), in the commutative-square form used here. Berkovich's proof
works by induction and reduction to standard étale maps. The proof
here instead glues local lifts given on finitely many lift charts.

## Locality lemmas

The first section holds for arbitrary saturated atlas presentations `S`
and `T` and an index type `ι`.

- `pullback_eq_of_eq` states that equal strong maps have equal pullbacks
  at a pair of charts, whichever admissibility proofs are used.
- `originalDomainStrongMap_comp_inclusion_comp` handles original chart
  domains `U ≤ V` of `S` and a strong map `f : S ⟶ T`. Restricting from
  `U` to `V`, then including `V` and applying `f`, equals including `U`
  and applying `f`. Both sides are rewritten as restrictions of `f` to
  subspaces, using the Library lemmas
  `originalDomainInclusion_comp_eq_restrictSubspace`,
  `originalDomainStrongMap_comp_eq_restrictOriginalDomain` and
  `StrongHom.restrictSubspace_restrictOriginalDomain`.
- `eq_of_originalDomainCover` takes a family `D`, indexed by `ι`, of
  original chart domains of `S` such that every chart of `S` lies in some
  member (`OriginalDomainCoversCharts D`).
  Two strong maps `a b : S ⟶ T` that agree after composing with every
  inclusion of a `D k` are equal. Each map is the gluing of its own
  restrictions (`StrongHom.toOriginalDomainStrongMatchingFamily_glue`),
  and the two restriction families are equal.
- `StrongNear.of_originalDomainCover` states that the test relation is
  local for such a family. Suppose `StrongNear τ` holds between the
  restrictions of `a` and `b` to every `D k`. Then it holds between `a`
  and `b`. Every point and every chart of `S` lies in some `D k`. The
  three conditions of `StrongNear` are checked there: equal preimages of
  the test domain, test pieces covering that preimage, and the spectral
  bound on each test piece. The charts of the subspace `D k` are charts
  of `S` lying in `D k`, with the same algebras and pullbacks.
- `locallyRefines_charts_into` takes a strong map `x : S ⟶ T` and target
  charts `c k` whose ranges locally refine the whole target. It shows
  that the source charts `q` that `x` sends into some `c k` have ranges
  locally refining the whole source. The family of preimages of the
  ranges of the `c k` locally refines the whole source
  (`LocallyRefines.preimage`). The preimage of a single chart range is
  an original chart domain (`StrongHom.isOriginalChartDomain_preimage`),
  so it is locally refined by the source charts that `x` sends into
  that chart. Transitivity of local refinement then finishes the proof.

## The gluing theorem

`hasStrongNearLifts_of_liftCharts` assumes that the space of the
saturation of `A` is Hausdorff. It also assumes that `g` has a finite
cover by lift charts (`HasFiniteLiftChartCover g`, from Worker 786's
module `QuasiEtaleLiftChartCover`) and that its localization is rigid
(`IsRigid`, the uniqueness half of Key Lemma 7.2 in the Library).
The conclusion is `HasStrongNearLifts g`.

Let `E` be a finite set of test triples on the saturation of `A`, and
let `s` be the finite set of lift charts. Rigidity provides a finite
set `Erig` of test triples. Put `E' = E ∪ Erig`. The proof proceeds as
follows.

1. For each lift chart `c` in `s`, the module `ChartTestTransfer`
   (`exists_globalChart_tests_strongNear`) gives finitely many functions
   `F c` on `c` and a bound `ε c`. For strong maps from a source with a
   global chart that send this chart into `c`, closeness of the
   pullbacks on `F c` within `ε c` implies `StrongNear τ` for every `τ`
   in `E'`.
2. The lift chart property of `c` gives a target chart `w c` containing
   the image of `c`. For `F c` and `ε c` it also gives finitely many
   functions `G c` on `w c` and a bound `δ c`.
3. The set `D` collects, for every `c` in `s`, the test triple with
   domain `w c`, function `0` and bound `1`, together with the test
   triples with domain `w c`, function `h` in `G c` and bound `δ c`.

Now let `x : S ⟶ ofSaturation A` and `y : S ⟶ ofSaturation B` satisfy
`StrongNear τ y (x ≫ g)` for every `τ` in `D`. Let `ι` be the type of
pairs `q = (c, P)` of a lift chart `c` in `s` and a chart `P` of `S` with
`x` sending `P` into `c`.

- `x ≫ g` sends `P` into `w c`. By the test triple with function `0`,
  the preimages of `w c` under `y` and `x ≫ g` agree, so `y` also sends
  `P` into `w c`. The other test triples in `D` bound the differences of
  the pullbacks of `G c` at `(P, w c)` by `δ c`. The lift chart property
  then gives a bounded map `a q : O(c) → O(P)` with
  `(a q) ∘ g* = y*` at `(P, w c)` and with values on `F c` within `ε c`
  of those of `x*`.
- Let `Dq q` be the original chart domain given by the range of `P`. Its
  subspace presentation has a chart `P₀ q` with range the whole space.
  The Library's `chartSourceMap` turns `a q` into a strong map
  `χ q : S.originalDomain (Dq q) ⟶ ofSaturation A`.
- `χ q ≫ g` is the restriction of `y` to `Dq q`
  (`chartSourceMap_comp`, `chartSourceMap_eq`).
- `χ q` is `E'`-near the restriction of `x` to `Dq q`. Its pullback at
  `(P₀ q, c)` is `a q` (`chartSourceMap_pullback_global`), so step 1
  applies.
- On the intersection of `Dq q` and `Dq q'`, the restrictions of `χ q`
  and `χ q'` agree. Both are `Erig`-near the restriction of `x` there.
  After composing with `g`, both equal the restriction of `y`. Rigidity
  makes their images in the localized category equal, and the
  localization functor is injective on maps between saturated
  presentations (`localizationFunctor_map_injective`).

The `χ q` thus form an `OriginalDomainStrongMatchingFamily`. The ranges
of the `Dq q` locally refine the whole source, by
`locallyRefines_charts_into` and the lift chart cover. The Library's
refined gluing (`domainCoverSourceSelection`, `refinedGlue`) gives a
refining subpresentation `S'` of `S`, whose inclusion
`r : S' ⟶ S` is a quasi-isomorphism, and a strong map `x' : S' ⟶ A`
restricting to `χ q` on every `Dq q`. The images of the `Dq q` in `S'`
contain every chart of `S'` (`domainCoverSourceSelection_coversCharts`).
So `x' ≫ g = r ≫ y` follows from `eq_of_originalDomainCover`. For `τ`
in `E`, `StrongNear τ x' (r ≫ x)` follows from
`StrongNear.of_originalDomainCover`, using that the test relation is
preserved by precomposition (`StrongNear.precomp`).

## The quasi-étale case

`IsQuasiEtale.hasStrongNearLifts` applies the gluing theorem. The lift
chart cover is Worker 786's `IsQuasiEtale.hasFiniteLiftChartCover`.
Rigidity is the Library's `isRigid_of_quasiEtale`, applied to the
localization of `g` with the compact Hausdorff source.
