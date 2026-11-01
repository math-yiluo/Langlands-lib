# Connecting the published projective-space chart APIs

This internal adapter connects the existing Library polynomial-Proj projective
space with the already published `AlgebraicGeometry.ProjSpace` chart API. It
works for every commutative ring `R : Type u` and every `n : ℕ`, including the
zero ring and `n = 0`. All imported Lean/Markdown pairs are preserved.

The imported `ProjectiveSpace.Structure` supplies
`projectiveSpaceConstantsEquiv`, `projectiveSpaceCoordinateRing_finiteType` and
`projectiveSpaceToSpec_isProper`. The imported
`ProjectiveSpace.CoordinateCoverProof` supplies coordinate affineness, the
irrelevant-ideal bound and coverage. The imported
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` supplies the
actual chart algebras, ratios, affine cover, monomial formula and
`adjoin_range_ratio`. These results are used under their existing names.

The new declarations have the following meanings and proofs:

- `toSpec_eq_projSpace_π` identifies `projectiveSpaceToSpec R n` with the
  published `AlgebraicGeometry.ProjSpace.π R n`. Both are the Proj structure
  morphism to the degree-zero spectrum followed by the spectrum of the
  constant-polynomial map. Lean checks their equality by reflexivity.
- `affineOpenCover R n` is an abbreviation for the published
  `AlgebraicGeometry.ProjSpace.affineOpenCover R n`, with its type displayed as
  a cover of `ProjectiveSpace R n`. Its index set is `Fin (n + 1)` and its
  chart rings are the degree-zero homogeneous localizations away from `X j`.
  No new cover is constructed.
- `algebraAway` exposes the published `ProjSpace.algebraAway` instance with
  `projectiveSpaceGrading R n` in its type. Instance search does not unfold
  that wrapper to find the published instance on its own. This adapter
  directly uses the existing instance and its scalar action.
- `affineOpenCover_comp_toSpec` says that each chart map followed by the
  Library structure morphism is `Spec` of the published chart algebra map.
  The proof directly applies the existing `ProjSpace.awayι_comp_π`; the two
  projective spaces and their structure morphisms agree definitionally.
- `isOpenImmersion_affineOpenCover_f` exposes the existing open-immersion
  instance for each chart. The proof displays the chart as Mathlib's
  `Proj.awayι` and infers that instance.
- `affineOpenCover_opensRange` identifies the open range of chart `j` with
  `projectiveSpaceCoordinateOpen R n j`. Mathlib's `Proj.opensRange_awayι`
  gives this equality, since the latter is the basic open of `X j` for the
  same grading.

The provenance is internal: these are definitional comparisons and adapters
between published APIs, using Mathlib's general Proj chart facts. The imported
FLT module records the pinned source, its adaptations and the retained notices
in `licenses/Anthropic-FLT/`. This file reuses that published module rather
than porting its definitions or proofs again.

This is an intermediate geometric helper for the division-CM representability
task. The representing CM scheme and its natural moduli comparison remain to
be constructed.
