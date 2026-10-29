# Proof: the actual `𝒪(1)` on projective space is ample

`Langlands.AlgebraicGeometry.projectiveSpaceTwistOneAmple` proves exactly the published
proposition `ProjectiveSpaceTwistOneAmpleStatement.{u}` from
`Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleStatement`:

```lean
theorem projectiveSpaceTwistOneAmple : ProjectiveSpaceTwistOneAmpleStatement.{u}
```

The proposition says that for every commutative ring `R : Type u` and every `n : ℕ` there is a
line bundle `M` on `ProjectiveSpace R n` with `M.obj = twistOne R n` and `M.IsAmple`. The
published `Picard.LineBundle.IsAmple` asks that the scheme be quasi-compact and that each
point lie in the generation locus `L.sectionOpen s` of some section `s` of a positive actual
tensor power `tensorPow L.obj m`, with that whole locus an affine open.

The theorem has no hypotheses on `R` or `n`, so the zero ring and `n = 0` are included. The
statement pair and every published pair it imports are unchanged. The module declares only
this theorem: no auxiliary definitions, lemmas or instances.

## Imported published results

- `projectiveSpaceCoordinateCover R n` (module `...ProjectiveSpace.CoordinateCoverProof`):
  each coordinate open `projectiveSpaceCoordinateOpen R n i = D₊(X i)` is affine, the
  coordinate opens cover (`⨆ i, D₊(X i) = ⊤`), and `ProjectiveSpace R n` is compact.
- `projectiveSpaceTwistOneLocalFrames R n` (module `...ProjectiveSpace.TwistOneLocalFramesProof`);
  only its clause 2, `Picard.IsLocallyFreeRankOne (twistOne R n)`, is used.
- `projectiveSpaceCoordinateGenerationOpen R n i` (module
  `...ProjectiveSpace.CoordinateGenerationOpenProof`):
  `trivializationOpen (twistOne R n) (twistOneCoordinate R n i) = D₊(X i)`.
- `Langlands.SchemeModule.trivializationOpen_mapIso` (module `...Picard.AmpleIsoProof`): for an
  isomorphism `e : P ≅ Q` of module sheaves and a global section `s` of `P`,
  `trivializationOpen Q (e.hom.app ⊤ s) = trivializationOpen P s`.
- `Langlands.Scheme.Modules.tensorRightUnitor M : tensorObj M (structureSheaf X) ≅ M`.

## Implemented proof

Fix `R` and `n`, and take the three facts of the coordinate cover.

1. **The witness.** Let `L` be the line bundle with underlying module `twistOne R n` itself,
   together with the published local-rank-one proof. Then `L.obj = twistOne R n` holds by
   `rfl`, and the compactness part of `IsAmple` is the compactness from the coordinate cover.
2. **A coordinate open containing the point.** For a point `x`, the cover equality puts `x` in
   `⨆ i, D₊(X i)`, so `Opens.mem_iSup` gives an index `i` with `x ∈ D₊(X i)`.
3. **The section.** Use the tensor power `m = 1`. The first actual tensor power
   `tensorPow (twistOne R n) 1` is definitionally `tensorObj (twistOne R n) (structureSheaf _)`.
   The proof does not identify this module with `twistOne R n` silently. It takes
   `s := (tensorRightUnitor (twistOne R n)).inv.app ⊤ (twistOneCoordinate R n i)`, the image of
   the coordinate section `X i` under the inverse of the right unitor.
4. **Its generation locus.** `L.sectionOpen s` is by definition
   `trivializationOpen (tensorPow (twistOne R n) 1) s`. The inverse unitor is the forward
   map of the isomorphism `(tensorRightUnitor (twistOne R n)).symm`, so
   `trivializationOpen_mapIso` rewrites this open to
   `trivializationOpen (twistOne R n) (twistOneCoordinate R n i)`. The published
   generation-open equality rewrites that to `D₊(X i)`. Hence `L.sectionOpen s = D₊(X i)`.
5. **Conclusion.** With `m = 1` (so `1 ≤ m`) and this `s`, the point `x` lies in
   `L.sectionOpen s` because `x ∈ D₊(X i)`, and `L.sectionOpen s` is affine because `D₊(X i)`
   is affine by the coordinate cover. Both facts are transported along the equality of step 4.

This is the route recorded in the statement's Markdown. A private conditional version, with
the local-rank-one proof and the generation-open equality as hypotheses, was compiled first.
This module replaces both hypotheses by the published theorems named above and keeps no
outer hypothesis.

## Check

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` builds the module with no
errors or warnings. The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
