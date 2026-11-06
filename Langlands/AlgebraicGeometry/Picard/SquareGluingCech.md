# Čech gluing of locally realized actual square gluing data

This internal helper module proves the general gluing step behind essential
surjectivity in the proof of `FieldPicardInfinitesimalGluingStatement`. Fix a
commuting square `S` of schemes and an actual gluing datum `D : S.GD`. Suppose
`D` is realized locally on a cover by cartesian open cubes, and the comparison
is full and faithful on all such cubes. Then `D` is realized by an actual line
bundle on `S.X`. Namespace:
`Langlands.AlgebraicGeometry.Picard.SquareGluingDescent`. The development is
internal; it follows no literature source. The notation is that of
`SquareGluingCubes`, `SquareGluingDescent`, `SquareGluingRespect` and
`SquareGluingLegs`.

## Hypotheses

- `FFOnCart S` holds when, for every square `T` and every cartesian cube
  `c : CubeMap S T` whose total map `c.t` is an open immersion, the comparison
  `T.C` is full and faithful.
- The family consists of an index type `ι : Type u`, squares `T : ι → Sq`,
  cubes `c i : CubeMap S (T i)` whose total maps are open immersions,
  `cart : ∀ i, (c i).Cart`, and `hcov : ∀ x, ∃ i y, (c i).t y = x`.
- The local realizations are actual line bundles `N i` on `(T i).X` with
  isomorphisms `ρ i : (T i).C.obj (N i) ≅ (c i).R.obj D` in `(T i).GD`. They
  are passed as separate families, not as fields of a structure.

The instances `isOpenImmersion_fstC`, `isOpenImmersion_sndC` and
`isOpenImmersion_comp` say that the overlap and composite cubes again have
open-immersion total maps.

## Covers

`covers₁`, `covers₂` and `covers₀` show that the leg maps `(c i).g₁` and
`(c i).g₂` and the corner maps `(c i).g₀` are jointly surjective. They use
cartesianness and `isPullback_exists_preimage`. `coverT`, `cover₁`, `cover₂`
and `cover₀` are the resulting open covers, built with `Scheme.Cover.mkOfCovers`.
On the leg and corner covers, open immersion follows from cartesianness.

## Overlaps and transitions

The pairwise overlap of `i` and `j` is the square `PB (c i) (c j)`, with
projection cubes `fstC` and `sndC`. Its total scheme is literally
`pullback (c i).t (c j).t`, which is also the pairwise overlap of `coverT`.

- `ff_overlap`: the comparison of each pairwise overlap square is full and
  faithful, since the composite overlap cube is cartesian.
- `tau i j` is the transition between the pullbacks of `N i` and `N j` to the
  overlap. It is the preimage under the full comparison of
  `pb (c i) (fstC ..) (ρ i)` followed by the inverse of
  `pb (c j) (sndC ..) (ρ j)`. `resp_tau` says that it respects these two
  pulled-back realizations.

The triple overlap of `i`, `j`, `k` is the square
`PB (fstC (c i) (c j)) (fstC (c i) (c k))`. Its projection cubes `A3` and `B3`
come from the overlaps `ij` and `ik`. The cube `Q3` from the overlap `jk` is
`PB.lift` of two composite cubes, which agree by `triple_eq`.

- `cocycle_pic` is the cocycle identity for the transitions in the actual
  Picard groupoid, written with the square comparisons of the triple overlap.
  Both sides respect the same two realizations on the triple overlap, by
  `Resp.along`, `resp_sqH` and `Resp.comp`. They are equal by `Resp.unique`,
  since the comparison of the triple-overlap square is faithful.
- `cocycle_mod` is the same identity for the underlying modules, via `mh_sqH`.
- `trans` gives the transitions as module isomorphisms on the overlaps of
  `coverT`. `cocycle` states the published
  `OpenCoverModuleGluing.CocycleCondition` for them.

## Gluing

- `gd` is the published `LineBundleGluingData` on `coverT` with bundles
  `(N i).of` and transitions `trans`. `glued` is its glued actual line bundle.
- `sig i` identifies the pullback of `glued` along `(c i).t` with `N i`, from the
  published `moduleIso`. `sig_compat` says that `sig` is compatible with `tau`
  through the square comparison, from the published `moduleIso_compatible`.
- `Psi i` is the local arrow `(c i).R.obj (S.C.obj glued) ⟶ (c i).R.obj D`
  given by `(cIi (c i) glued).inv ≫ (T i).C.map (sig i) ≫ (ρ i).hom`.
  `Psi_compat` says that the local arrows agree on pairwise overlaps (from
  `legs_compat`).
- `exists_left` and `exists_right` glue the first legs and the second legs of
  the `Psi i` over `cover₁` and `cover₂`. They give actual isomorphisms
  `l : (S.C.obj glued).left ≅ D.left` and `r : (S.C.obj glued).right ≅ D.right`
  restricting to the legs of `Psi i`. The tools are the published
  `openCoverIsoGluing_of_homGluing` and
  `OpenCoverHomGluing.openCoverHomGluing`, with compatibility from `leg_left`
  and `leg_right`.
- `exists_iso`: `∃ L : PicardGroupoid S.X, Nonempty (S.C.obj L ≅ D)`, with
  `L = glued`. The isomorphism is `Comma.isoMk l r`. Its corner square is checked
  on `cover₀` by the published `LineBundleIsoDescent.hom_ext_of_openCover`. On
  each piece of that cover it is `map_w` applied to `Psi i`.
