# Torsion bracket maps from Lefschetz's embedding theorem

This module proves the published `TorsionBracketMapStatement` from the published
`CubicFieldEmbeddingStatement`. Here `CubicFieldEmbeddingStatement` is
Lefschetz's theorem for the canonical cubic bundle over fields. The result is a proved definition of the
implication; it does not prove `TorsionBracketMapStatement` outright.

## Charts on the frame locus

- `lastComplEquiv m` identifies `Fin (m + 1)` with the indices of
  `Fin (m + 2)` other than the last, by `Fin.castSucc`.
- `Datum.exists_bracketChart` takes a point `x` of the projective frame locus of
  a label family `ρ : Fin (m + 2) → labels`. It produces a bracket chart
  (`EvaluationBracket.Chart`) for the torsion evaluations of the datum with
  `m + 1` frame labels `ρ ∘ Fin.castSucc` whose open contains `x`. By the
  definition of the frame locus, `x` lies in an open `W₀` on which the frame
  evaluation omitting the last label becomes an isomorphism after pullback.
  `OpenSectionProducts.bijective_pi_app_of_isIso_pullback` turns this into
  bijectivity of joint evaluation over every open inside `W₀`. Each torsion
  evaluation line `(pullback (torsionPoint r)).obj cubicBundle` is a line bundle
  and has a generator near `x` (published
  `BiCech.exists_isFrameOn_of_isLocallyFreeRankOne`). The chart open is `W₀`
  intersected with the finitely many generator opens.

## Field models of a datum

`Datum.fieldModel hd a t` is the `EvaluationBracket.FieldModel` of a datum `a`
over a locally noetherian base at a point `t : Spec K ⟶ S`, for `K`
algebraically closed. It consists of the following.

- The evaluation data of the pulled-back datum `a.pullback t`.
- The source comparison: the published cubic direct-image base-change map, an
  isomorphism by `cubicDirectImage`.
- The target comparisons: `torsionEvaluationBaseChangeIso`.
- The compatibility, which is
  `rigidificationBaseChangeMap_comp_torsionEvaluation`.
- Quasi-coherence, from finite local bases and from local freeness of rank one.
- `finrank = 6^g d` (`finrank_cubicSections`) and `finrank = 1` for the lines
  (`finrank_moduleSpecΓ_lineBundle`).

Equivalence of two field models is, by definition, the published
`Datum.TorsionConfigurationEquivalent` of the two pulled-back data.

## The reduction

`torsionBracketMap_of_cubicFieldEmbedding hL : TorsionBracketMapStatement`
works as follows for positive `g` and `d`.

1. Take the bound `N` of `frameLocusCover_of_cubicFieldEmbedding hL
   frameLocusBaseChange` and use `max N 1`.
2. For a level `n` at least this bound, a level base `T` and a datum `b`, every
   point of `T` lies in a projective frame locus. Choose a bracket chart around
   every point.
3. Trivialize the `n`-th tensor powers of the evaluation lines by the published
   `Datum.torsionEvaluationLinePowerIso`, transported by
   `TensorPowerGauge.tensorPowComparison`. Enumerate the tuples of
   `6^g d` labels.
4. Take `j` to be the glued morphism `CoordinateAtlas.atlasMap`, with structure
   map `LevelBase.toLocalizationSpec` to `Spec ℤ[1/n]`. The number `m` is the
   number of label tuples minus one.
5. For an algebraically closed field `K : Type` and a `K`-point `y`,
   `EvaluationBracket.exists_finset_equivalent` with the field models
   `b.fieldModel hd` gives the required finite set.

No quasi-compactness of `T` and no representability is used.

## Provenance

This is internal and not taken from a literature source. It follows the
intended proof recorded in the Markdown of the published
`TorsionBracketMapStatement`. Generation of the
bracket coordinates comes from the published frame-locus cover rather than
directly from the torsion hyperplane bound. The coordinates are glued from
local charts rather than taken as sections of a determinant line bundle.
