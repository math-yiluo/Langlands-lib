# Gluing analytic spaces along open subspaces

The theorem
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation.exists_glued`
proves that gluing data along open subspaces have a glued analytic space. Let
`K : Type u` be a complete ultrametric normed field (trivial valuations allowed)
and `R : LocalizedOpenRelation K` gluing data in relation form (module
`LocalizedOpenRelation`): analytic spaces `Z m` of `LocalizedCategory.{u, u, u}`,
spaces `S m n` with open immersions `a m n : S m n → Z m`, `b m n : S m n → Z n`,
reflexive, symmetric and transitive on morphisms from every test space. Then there
are `Y : LocalizedCategory.{u, u, u}` and morphisms `ι m : Z m ⟶ Y` such that

1. every `ι m` is an open immersion (`openImmersion`);
2. the `ι m` are jointly surjective on underlying points;
3. for all `m n`, `IsPullback (a m n) (b m n) (ι m) (ι n)`.

The witness is `glued R` with the morphisms `ιL m` (module
`LocalizedOpenRelationQuotient`).

## Proof

- `cmap_ιL`: for a chart `c` of a piece and a chart image `T` of the glued space with
  `c.image ⊆ T ⊆ pieceRange c.m`, `cmap S c φ ≫ ιL c.m` is the chart map into `T`
  of `φ.comp (rho c T.rep _)` (`ymap`). Proof: compose the small-spectrum chart map
  with `pieceMap` and with the domain inclusion (`chartMap_comp` twice); the
  pullbacks are `rho` and an identity restriction.
- `domW m n`, `nuW m n` and `tauW m n` are the open domain `domainSet m n` of `Z m`,
  its inclusion, and the transfer of that inclusion to `Z n`
  (`rel_nuW_tauW`). `smallChart_nuW`: a chart of the domain followed by `nuW` is the
  inclusion of the same chart of `Z m`.
- `CoverIndex m n` consists of a chart of `domW m n` and a chart of `Z n` whose
  image contains the image of the first. `coverIndex_locallyRefines`: these charts
  cover the domain. At a point `z` related to `z'` in `Z n`, take finitely many
  charts of `Z n` around `z'` covering a neighbourhood; the traces on `Z m` of their
  images are analytic domains around `z`
  (`isOriginalChartDomain_preimage_image`); their charts around `z` cover a
  neighbourhood of `z` in each trace, and together a neighbourhood of `z`, because
  the traces cover the preimage of the image of a neighbourhood of `z'`.
- `nuW_ιL`: `nuW m n ≫ ιL m = tauW m n ≫ ιL n`, checked on this cover with
  `localizedHom_ext_of_chartCover`. For an index with charts `c` of `Z m` and `d`
  of `Z n`, the transfer of `incl c` is `cmap c.alg d (rho c d _)` (`Rel.unique`
  with `rel_rho`). Both composites are chart maps into the chart image `d.image`
  by `cmap_ιL` and `SmallAffinoidSpectrum.chartMap_of_subset`, with the same
  bounded map `rho c (rep d.image)` by `rho_comp`.
- `Rel.ιL_eq`: related morphisms `f : T ⟶ Z m` and `g : T ⟶ Z n` satisfy
  `f ≫ ιL m = g ≫ ιL n`: `f` factors through `domW m n`, `g` is the corresponding
  factor followed by `tauW m n` (`Rel.unique`), and `nuW_ιL` applies. In particular
  `a m n ≫ ιL m = b m n ≫ ιL n` (`a_ιL_eq_b_ιL`).
- `isPullback_ιL`: for a cone `(s.fst, s.snd)` over `ιL m` and `ιL n`, the points of
  `s.fst` lie in `domainSet m n` (`ιL_apply`, `preimage_range_ι`), so `s.fst`
  lifts through the open immersion `a m n`; the lift followed by `b m n` is related
  to `s.fst`, so it agrees with `s.snd` after `ιL n` by `Rel.ιL_eq`, hence equals it
  because `ιL n` is a monomorphism; uniqueness holds since `a m n` is a monomorphism.
- Joint surjectivity: `exists_ι_eq` and `ιL_apply`.

## Provenance

Derived. This is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), Proposition 1.3.3, case a), printed p.24 / PDF p.21
(`berkovich-1993-etale-cohomology`): the space obtained by gluing analytic spaces
along open analytic domains exists, each piece is isomorphic to an open analytic
domain of it, the pieces cover it, and two pieces meet in the image of their
gluing domain (properties (1)–(4) on that page). Property (3) and the compatibility
(4) are recorded here as the pullback squares. The gluing step of Conrad–Temkin,
*Non-archimedean analytification of algebraic spaces* (2009), proof of Lemma 4.2.3,
printed p.21 (`conrad-temkin-2009-nonarchimedean-analytification`), uses this
construction. Uniqueness of the glued space is not stated here.
