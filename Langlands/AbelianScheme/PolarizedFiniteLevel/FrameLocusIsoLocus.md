# The projective frame locus as an intersection of stalk-isomorphism loci

This internal module describes the published `Datum.frameLocus` (module
`FrameLocus`) pointwise. All schemes lie in one universe `u`.

## Results

- `mem_sSup_isIso_restrict_iff`: for a family of morphisms `φ k` of module
  sheaves on `S`, consider the supremum of all opens `W` on which every
  `(pullback W.ι).map (φ k)` is an isomorphism. A point lies in it exactly when
  it has an open neighbourhood contained in every iso locus `isoLocus (φ k)`.
  An isomorphism is detected on stalks
  (`isIso_iff_forall_mem_isoLocus`). Restriction to an open is a flat
  pullback, which does not change stalk maps (`mem_isoLocus_pullback_iff`).
- `Datum.hasFiniteLocalBasis_frameTarget`: the target of a frame evaluation is
  the product of the line bundles `(a.torsionPoint (ρ j))^* L³`. It has finite
  local bases, by `isLocallyFreeOfRank_pi`
  (module `Picard/LineBundleFiniteProduct`).
- `Datum.coe_frameLocus`: suppose the cubic direct image
  `a.rigidificationModule` has finite local bases. Then, as a set, the frame
  locus of `ρ` is the intersection over `k` of the iso loci of
  `a.frameEvaluation ρ k`. Each iso locus is open, by the published
  `isOpen_isoLocus`: source and target are locally finitely presented (published
  `isFinitePresentation_of_hasFiniteLocalBasis`). A finite intersection of
  opens is open, so the open intersection itself is one of the opens in the
  supremum.

## Provenance

Internal. It uses the published modules `FrameLocus`, `StalkIsoLocus` and
`FiniteLocalBasisDescent`, and the internal modules `IsoLocusPullbackFree` and
`Picard/LineBundleFiniteProduct`.
