# The proper-field Picard algebraic space from a Picard stack atlas

Author: Worker 3502.

This module reduces the exact Library proposition
`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement.{u}`
to the single proposition
`Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasStatement.{u}`.
Every other input of the published conditional assembly is discharged here by a
published proof. The module does not prove either proposition.

## Declarations

All declarations are in the namespace `Langlands.AlgebraicGeometry.Picard` and
keep the single universe parameter `u`.

- `fieldEtaleFppfClassSheaf_of_stackAtlas (hA : FieldPicardStackAtlasStatement.{u}) :
  FieldEtaleFppfClassSheafStatement.{u}`. Under the stack-atlas hypothesis, for
  every field `k : Type u` and every proper `X : Over (Spec (CommRingCat.of k))`,
  the presheaf `RelativePicard.etaleClassSheafPresheaf X.hom` is a sheaf for
  `Scheme.fppfTopology.over (Spec (CommRingCat.of k))`.
- `fieldPicardSheafAlgebraicSpace_of_stackAtlas (hA : FieldPicardStackAtlasStatement.{u}) :
  FieldPicardSheafAlgebraicSpaceStatement.{u}`.
- `fieldPicardSheafAlgebraicSpace_of_coherentStackAtlas
  (h : CoherentSheaves.FieldCoherentStackAtlasStatement.{u}) :
  FieldPicardSheafAlgebraicSpaceStatement.{u}`.
- `fieldPicardSheafAlgebraicSpaceOfStackAtlas`, a definition whose type is the
  implication `FieldPicardStackAtlasStatement.{u} → FieldPicardSheafAlgebraicSpaceStatement.{u}`.
  Its value is the theorem above. It exists so that the record has a single entry
  declaration carrying the whole reduction.

## Proofs

**Fppf descent of the etale class sheaf.** Fix `k`, `X` and the hypothesis `hA`.
The published theorem `fieldEtalePicardAtlas_of_stackInputs` (module
`Picard.FieldPicardAtlasAssembly`), applied to `hA` and
to the published proof `smoothAutomorphismEtaleAtlas` of
`SmoothAutomorphismEtaleAtlasStatement`, gives two facts about the presheaf
`F = RelativePicard.etaleClassSheafPresheaf X.hom`. First, `F` has a diagonal
represented by schemes (`AlgebraicSpace.HasRepresentableDiagonal`). Second, there
are a scheme `U` over `Spec k` and a transformation from the functor of points of
`U` to `F` that is etale and surjective in the Library's sense
(`AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`). The local finite type
part of that conclusion is not used here. By definition `F` is the underlying
presheaf of the etale sheafification `RelativePicard.etaleClassSheaf X.hom`, so
`F` is a sheaf for `Scheme.etaleTopology.over (Spec k)`; this is the `property`
field of that sheaf. The published theorem `AlgebraicSpace.etaleAtlasFppfSheaf`
(module `AlgebraicSpace.EtaleAtlasFppfSheafProof`) proves
`AlgebraicSpace.EtaleAtlasFppfSheafStatement`: an etale sheaf on `Over S`
with representable diagonal and a surjective etale scheme atlas is a sheaf for the
fppf topology on `Over S`. Applying it to `F` gives the claim.

**The algebraic-space target.** The published theorem
`fieldPicardSheafAlgebraicSpace_of_stackInputs`, in module
`Picard.FieldPicardClosedDiagonal`, proves the exact target from four inputs:

1. `FieldPicardClassEqualizerImmersionStatement`, discharged by the published proof
   `RelativePicard.fieldPicardClassEqualizerImmersion` (module
   `Picard.TrivialLocusNoetherian`);
2. `FieldPicardStackAtlasStatement`, the hypothesis `hA`;
3. `SmoothAutomorphismEtaleAtlasStatement`, discharged by the published proof
   `smoothAutomorphismEtaleAtlas` (module `Picard.SmoothAutomorphismEtaleAtlasProof`);
4. `FieldEtaleFppfClassSheafStatement`, discharged by
   `fieldEtaleFppfClassSheaf_of_stackAtlas hA` above.

So `fieldPicardSheafAlgebraicSpace_of_stackAtlas hA` is that theorem applied to
these four terms.

**The coherent-stack variant.** The published lemma
`fieldPicardStackAtlas_of_coherentStackAtlas` (module `Picard.CoherentAtlasTransfer`)
derives `FieldPicardStackAtlasStatement.{u}` from
`CoherentSheaves.FieldCoherentStackAtlasStatement.{u}`. Composing it with the
previous theorem gives `fieldPicardSheafAlgebraicSpace_of_coherentStackAtlas`.

## Scope

The hypotheses are exactly the displayed propositions. No assumption is added on
the field (it may be imperfect) or on the proper scheme `X`: no projectivity,
smoothness, reducedness, connectedness, rational point, chosen section, universal
bundle, or identification of `H⁰(X, 𝒪_X)` with `k`. The sheaf in the conclusion is
the published fppf sheafification `RelativePicard.classSheaf X.hom` on all schemes
over `Spec k`, and all of its sections are covered, through the published
statement's definition. The universe `u` is unchanged.

None of the four inputs uses `FieldPicardSheafAlgebraicSpaceStatement` or
`FieldPicardSheafRepresentabilityStatement`, so the reduction is not circular.

## Provenance

This is an internal reduction by composition of published Library results. It
states no new external theorem and cites no new source. The observation that the
etale-to-fppf comparison follows from the stack atlas is internal: once the etale
class sheaf has an etale scheme atlas and a representable diagonal, fppf descent
follows from the published general theorem on such etale sheaves. The remaining
open input, `FieldPicardStackAtlasStatement`, is the target of a separate proof
task.
