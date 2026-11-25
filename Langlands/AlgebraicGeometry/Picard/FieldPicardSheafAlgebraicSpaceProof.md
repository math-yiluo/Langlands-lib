# The proper-field Picard sheaf is an algebraic space: proof

Module: `Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceProof`.

`Langlands.AlgebraicGeometry.Picard.fieldPicardSheafAlgebraicSpace` proves the
published proposition
`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement.{u}`
at every universe `u`. For every field `k : Type u` and every scheme
`X : Over (Spec (CommRingCat.of k))` with `IsProper X.hom`, it gives:

- `AlgebraicSpace.IsAlgebraicSpace (Spec k) (RelativePicard.classSheaf X.hom)`;
- `AlgebraicSpace.IsClosedImmersion (Limits.diag (RelativePicard.classSheafPresheaf X.hom))`;
- a scheme `U` over `Spec k`, locally of finite type, with a transformation from its
  functor of points to `RelativePicard.classSheafPresheaf X.hom` that is etale and
  surjective in the Library's sense.

The sheaf is the published fppf sheafification of ordinary line-bundle classes on all
schemes over `Spec k`.

## Proof

The proof is the composition of two published Library theorems.

1. `fieldPicardSheafAlgebraicSpace_of_stackAtlas` (module
   `Picard.FieldPicardSheafAlgebraicSpaceReduction`) proves
   `FieldPicardStackAtlasStatement.{u} → FieldPicardSheafAlgebraicSpaceStatement.{u}`.
   It discharges every other input by published proofs: the closed class-equalizer
   locus (`RelativePicard.fieldPicardClassEqualizerImmersion`), the etale atlas of
   the quotient by smooth automorphism groups (`smoothAutomorphismEtaleAtlas`), and
   fppf descent for the etale class sheaf, obtained from the stack atlas and
   `AlgebraicSpace.etaleAtlasFppfSheaf`. Its Markdown gives the details.
2. `fieldPicardStackAtlas` (module `Picard.FieldPicardStackAtlasProof`) proves `FieldPicardStackAtlasStatement.{u}`:
   the actual relative line-bundle groupoid of a proper scheme over any field has a
   smooth surjective scheme atlas locally of finite type over the field. It is
   itself an assembly of published proofs: `fieldPicardStackAtlas_of_finiteType`
   applied to `PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` with
   `finiteTypeFormalVersalBundle`, `versalAlgebraization_of_etaleApproximation`
   `CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation` and
   `picardOpennessOfVersality`.

Applying the first theorem to the second gives the target.

## Scope

No hypothesis is added: the field is arbitrary (imperfect fields included), `X` is
an arbitrary proper scheme, and no projectivity, smoothness, reducedness,
connectedness, rational point, section, identification of `H⁰(X, 𝒪_X)` with `k`,
universal bundle or Picard representability is assumed. In particular neither input
uses `FieldPicardSheafRepresentabilityStatement`. The universe `u` is preserved.

## Provenance

Internal assembly of published Library results; it states no new external theorem.
The mathematical route (algebraicity of the Picard stack, Stacks Project Proposition
99.10.2, Tag 0D04, and Artin's 1974 correction of Artin I, Appendix item 2) is
explained in the Markdown of the two inputs.
