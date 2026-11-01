# Cohomology of an external tensor product of line bundles via Čech complexes

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth`.
This is the geometric input to the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

## Frames and covers

- `exists_isFrameOn_of_isLocallyFreeRankOne`: a locally free sheaf of rank one has a frame
  near every point. Its local trivialization `M|_T ≅ 𝒪_T` becomes a pullback
  trivialization by `Scheme.Modules.restrictFunctorIsoPullback`. The ported FLT theorem
  `Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit` then gives a frame.
- `exists_frameCover`: a quasi-compact scheme with a locally free sheaf of rank one `L`
  has a finite ordered affine cover with a frame of `L` on each member. The affine opens
  carrying a frame form a basis, and compactness gives a finite subcover. The construction
  follows the Library's `Scheme.OrderedAffineCover.ofCompactSpace`.
- `frames_inter`: frames on the members restrict to frames on all finite intersections.
- `isLocallyFreeRankOne_extTensor`: for any `f`, `g`, the module `p₁^* L ⊗ p₂^* M` is
  locally free of rank one when `L` and `M` are. Near a point, the cup of local frames is
  a frame (`isFrameOn_cup`). By the FLT theorem `IsFrameOn.nonempty_pullback_iso_unit`,
  this gives a local trivialization. This avoids the Library's
  `IsLocallyFreeRankOne.tensor`, which assumes `pullbackTensorComparisonIsIsoStatement`.

## Main results

`nonempty_relativeCohomology_extTensor_iso hπ hP hL hM 𝒰 𝒱 hfX hfY n` has the following
hypotheses:

- `πX`, `πY` and `πP` are separated;
- `L` and `M` are locally free of rank one;
- each member of `𝒰` carries a frame of `L`, and each member of `𝒱` a frame of `M`.

It states
`Nonempty ((relativeCohomology πP n).obj (p₁^* L ⊗ p₂^* M) ≅ (totCech πX πY 𝒰 𝒱 L M).homology n)`.
The proof combines three results:

1. quasi-coherence, by `isLocallyFreeRankOne_extTensor` and the Library's
   `IsLocallyFreeRankOne.isQuasicoherent`;
2. `BiCech.Comparison`, applicable because the opens `biOpen s t` are affine
   (`FieldTwoAxisH1Injectivity.isAffineOpen_prodOpen` and
   `CechResolution.isAffineOpen_inter`);
3. `sectionsIso`, transported to cohomology by `homologyFunctor`.

`exists_nonempty_relativeCohomology_overProd_iso X Y L M n` has the following setting:

- `K` is any commutative ring, and `X Y : Over (Spec (CommRingCat.of K))`;
- `X.hom` and `Y.hom` are separated, and `X.left`, `Y.left` are quasi-compact;
- `L` and `M` are line bundles.

It states that there exist `𝒰 : X.left.OrderedAffineCover` and
`𝒱 : Y.left.OrderedAffineCover` with an isomorphism

    (relativeCohomology (X ⨯ Y).hom n).obj
        (tensorObj (pullback prod.fst.left L.obj) (pullback prod.snd.left M.obj))
      ≅ (mapBifunctor (cechCochainComplex X.hom 𝒰 L.obj) (cechCochainComplex Y.hom 𝒱 M.obj)
          (curriedTensor _) (ComplexShape.up ℕ)).homology n

Two supporting lemmas:

- `isPullback_overProd`: the projections of the product form a pullback square of schemes
  (Mathlib's `Over.isPullback_of_binaryFan_isLimit`).
- `isSeparated_overProd`: `(X ⨯ Y).hom` is separated, by base change and composition.

The covers come from `exists_frameCover`.

Provenance: internal. This replaces the product-cover Čech comparison in the proof of the
Künneth formula (Stacks Project, Varieties, tag 0BED) by the bi-Čech resolution of
`BiCech.Complex`.
