# The quasi-étale condition at a point of a saturated presentation

Module `Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality`.

This module turns the Library's quasi-étale condition (`QuasiEtaleSite`) into a pointwise
condition. The condition is stated for any saturated atlas presentation `S` and any arrow
`ψ : localizationFunctor.obj S ⟶ Z` of the localized category. It then proves that the
condition is invariant under isomorphisms, can be pushed forward along open strong domain
embeddings, and characterizes `quasiEtale`. These are the ingredients of the quasi-étale half
of `Langlands.Analytic.SaturatedAtlasPresentation.SigmaDescStatement`. The module also proves
that a quasi-étale arrow followed by an étale arrow is quasi-étale.

Everything is in the namespace `Langlands.Analytic.SaturatedAtlasPresentation`, and `K` is a
complete ultrametric normed field. The two definitions below are internal: they copy the body of
the Library definition `IsQuasiEtaleAt` (Berkovich's quasi-étale condition at a point, as
formalized in `QuasiEtaleSite`), with the constructed saturation `ofSaturation A` replaced by an
arbitrary saturated presentation `S` and `localizationFunctor.map g` replaced by an arbitrary
arrow `ψ`. `isQuasiEtaleAt_iff` records that, for `S = ofSaturation A` and
`ψ = localizationFunctor.map g`, the new condition is literally `IsQuasiEtaleAt g`. There is no
further literature source; the results are internal lemmas about the Library's constructions.

## Definitions

- `IsQuasiEtaleChart S ψ i`: the chart `i` of `S` is a quasi-étale chart for `ψ`. That is, there
  are an object `W`, an étale arrow `w : W ⟶ Z` and an affinoid domain embedding
  `j : L(S.domain (S.chartDomain i)) ⟶ W` (`IsAffinoidDomainEmbedding`) with
  `j ≫ w = S.localizedDomainInclusion (S.chartDomain i) ≫ ψ`. Here `L` is `localizationFunctor`.
- `IsLocalizedQuasiEtaleAt S ψ y`: there is a finite set `σ` of subsets of the underlying space
  of `S` whose union is a neighbourhood of `y`, and each member of `σ` is the range of a
  quasi-étale chart for `ψ`.
- `isQuasiEtaleAt_iff`: for a strong map `g : ofSaturation A ⟶ ofSaturation B`,
  `IsQuasiEtaleAt g y` holds if and only if
  `(ofSaturation A).IsLocalizedQuasiEtaleAt (localizationFunctor.map g) y` does (`Iff.rfl`).

## Elementary properties (namespace `IsLocalizedQuasiEtaleAt`)

- `of_cover`: the condition at `y` holds as soon as a finite family `τ` of sets has a union that
  is a neighbourhood of `y`, and every member of `τ` is covered by finitely many ranges of
  quasi-étale charts. Proof: take the union over `τ` of the chosen finite chart families.
- `comp`: if `χ : Z ⟶ Z'` is an arrow such that `w ≫ χ` is étale for every étale `w` with
  target `Z`, then the condition for `ψ` at `y` implies the condition for `ψ ≫ χ` at `y`. The
  same charts work, with `w` replaced by `w ≫ χ`.
- `comp_etale`: the case of an étale `χ` (`etale_comp`).
- `comp_iso`: the case of an isomorphism `χ` (`etale_of_isIso`).

## Invariance under isomorphisms

- `isQuasiEtaleChart_iso_comp`: let `e : L S ≅ L S'` be an isomorphism, let `i'` be a quasi-étale
  chart of `S'` for `ψ`, and let `c` be a chart of `S` whose range lies in the preimage of the
  range of `i'` under the continuous map of `e.hom`. Then `c` is a quasi-étale chart of `S` for
  `e.hom ≫ ψ`.

  Proof. Let `D = domainPreimage e.hom (S'.chartDomain i')` be the analytic domain of `S` that
  is the preimage of the chart domain of `i'`. The Library gives an isomorphism
  `η : L(S.domain D) ≅ L(S'.domain (S'.chartDomain i'))` compatible with the inclusions and
  `e.hom` (`domainPreimageIso`, `domainPreimageIso_hom_inclusion`). The chart domain of `c` lies
  in `D`, so its inclusion lifts through `D` to an arrow `m` (`exists_localizedDomainLift`; the
  point condition uses `localizedSpaceFunctor_map_localizedDomainInclusion`). The new witness
  is `m ≫ η.hom ≫ j'` with the same étale arrow `w`. It is an affinoid domain embedding by
  `IsAffinoidDomainEmbedding.chart_comp` (module `LocalizedChartTransport`) applied to
  `j'` precomposed with the isomorphism `η`. The compatibility equation follows from those of
  `j'`, `η` and `m`.
- `IsLocalizedQuasiEtaleAt.of_iso`: for an isomorphism `e : L S ≅ L S'`, the condition for `ψ`
  at the image of `y` under `e.hom` implies the condition for `e.hom ≫ ψ` at `y`.

  Proof. Let `F` be the continuous map of `e.hom`. The preimages under `F` of the chart ranges
  in `σ'` form a finite family whose union is a neighbourhood of `y`. Each such preimage is the
  carrier of the analytic domain `domainPreimage e.hom (S'.chartDomain i')`. It is compact,
  because `F` is a homeomorphism (`TopCat.homeoOfIso` of `localizedSpaceFunctor.mapIso e`) and
  chart ranges are compact (`isCompactDomain_chartDomain`). So
  `exists_finite_charts_of_isCompact` covers it by finitely many charts of `S` contained in
  it. These charts are quasi-étale charts for `e.hom ≫ ψ` by `isQuasiEtaleChart_iso_comp`, and
  `of_cover` concludes.

## Pushforward along open domain embeddings

- `IsLocalizedQuasiEtaleAt.map_of_isDomainEmbedding`: let `t : N ⟶ Q` be a strong map of
  saturated presentations that is a domain embedding and has an open base map. If
  `localizationFunctor.map t ≫ ψ` satisfies the condition at `x`, then `ψ` satisfies it at
  `t.baseMap x`.

  Proof. Take the images under `t.baseMap` of the chart ranges in `σ`. Their union is the image
  of a neighbourhood of `x` (`Set.image_sUnion`), hence a neighbourhood of `t.baseMap x`, since
  the map is open. For a quasi-étale chart `c` of `N`, `exists_chart_iso_of_isDomainEmbedding`
  (module `LocalizedChartTransport`) gives a chart `d` of `Q` with range `t.baseMap '' range c`
  and an isomorphism `η` of chart domains compatible with `t`. Then `η.inv ≫ j` and the same
  `w` show that `d` is a quasi-étale chart for `ψ`.

## Characterization of quasi-étale arrows

- `isLocalizedQuasiEtaleAt_of_quasiEtale`: if `φ : L S ⟶ Z` is `quasiEtale`, it satisfies the
  condition at every point of `S`. By definition of `quasiEtale` there are a quasi-étale strong
  map `g : ofSaturation A ⟶ ofSaturation B` and an isomorphism of arrows between
  `localizationFunctor.map g` and `φ`. Its components are isomorphisms `ex` (sources) and `ey`
  (targets). By `isQuasiEtaleAt_iff` and `comp_iso`, `localizationFunctor.map g ≫ ey.hom`
  satisfies the condition at every point of `ofSaturation A`. `of_iso` along `ex.symm`, together
  with the commutative square of the arrow isomorphism, transports this to `φ`.
- `quasiEtale_of_forall_isLocalizedQuasiEtaleAt`: conversely, an arrow `ψ : L S ⟶ Z` that
  satisfies the condition at every point is `quasiEtale`. The Library's
  `exists_localizedRightFraction` writes `ψ` as a right fraction `L(φ.s)⁻¹ ≫ L(φ.f)` with a
  strong quasi-isomorphism `φ.s`. Composing `φ.f` with the comparison isomorphisms
  `saturationIso` gives a strong map
  `g : ofSaturation N.presentation ⟶ ofSaturation (presentationOf Z).presentation` with
  `L g = eN.hom ≫ ψ ≫ ε.inv` for isomorphisms `eN` and `ε`. The pointwise condition for `L g` is
  then given by `comp_iso` and `of_iso`, so `g` is quasi-étale (`isQuasiEtaleAt_iff`). The arrow
  isomorphism `Arrow.isoMk eN ε` between `L g` and `ψ` completes the witness of `quasiEtale ψ`.
- `quasiEtale_iff_forall_isLocalizedQuasiEtaleAt`: the two previous results combined.
- `quasiEtale_comp_of_etale`: if `φ : X ⟶ Y` is quasi-étale and `χ : Y ⟶ Z` is étale, then
  `φ ≫ χ` is quasi-étale. Use `S = presentationOf X`, then apply
  `isLocalizedQuasiEtaleAt_of_quasiEtale`, `comp_etale` and
  `quasiEtale_of_forall_isLocalizedQuasiEtaleAt`.
