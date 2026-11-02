# Generation opens of linear sections of `𝒪(1)` and of their pullbacks

This module is over a commutative ring `R` and natural number `n`, for
`ProjectiveSpace R n` with its twisting sheaf `twistOne R n`.

- `twistOneLinearSection R n f` is the global section `f / 1` of `𝒪(1)`
  attached to a linear form `f ∈ projectiveSpaceGrading R n 1`. It is the
  Library section `projTwistingSheafSection` in degree one.
- `twistOneLineBundle R n` packages `twistOne R n` as a `LineBundle`, using
  the published local frames `projectiveSpaceTwistOneLocalFrames`.
- `trivializationOpen_twistOneLinearSection`: the whole generation open
  (`trivializationOpen`) of `f / 1` is the basic open `D₊(f)`. The inclusion
  `D₊(f) ≤ …` is the published fact that `f / 1` trivializes `𝒪(1)` on
  `D₊(f)`. For the converse, take a point `x` in an open `V` where `f / 1`
  generates. Pick a coordinate chart `D₊(X j)` containing `x`. Write the
  restriction of the coordinate section `X j / 1` as `g · (f / 1)` on `V`
  (`LineBundleDescent.trivializesOn_iff_bijective`). Evaluating at `x` shows
  that `f / 1` is a unit in the localization at `x`, because `X j / 1` is one
  there. Hence `f` is not in the homogeneous prime of `x`
  (`IsLocalization.AtPrime.isUnit_to_map_iff`).
- `mem_trivializationOpen_twistOneLinearSection_iff`: `x` is in that open iff
  `f ∉ x.asHomogeneousIdeal`.

In namespace `Langlands.SchemeModule`:

- `isoPullbackSection g L e s` pulls a global section `s` of the line bundle
  `L` back along `g : Y ⟶ X` (`pullbackSection`). It then transports the result
  along an isomorphism `e : g^* L ≅ N` of `Y`-modules.
- `trivializationOpen_isoPullbackSection`: the generation open of
  `isoPullbackSection g L e s` is `g ⁻¹ᵁ` of the generation open of `s`. This
  combines the published `trivializationOpen_mapIso` with
  `lineBundlePullbackSectionOpen`.

## Provenance

These are internal comparisons between Library constructions: the twisting
sheaf section `projTwistingSheafSection`, the generation open
`trivializationOpen`, and section pullback. They correspond to the standard
facts `(ℙⁿ)_f = D₊(f)` and `(g^* s)` generates exactly on `g⁻¹ X_s`. They are
helpers for reducing
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(Mumford–Fogarty–Kirwan, GIT 3rd ed., Prop. 7.7) to a Bezout count. They do
not prove that target.
