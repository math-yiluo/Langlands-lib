# Assembling the Picard algebraic space of an abelian scheme from a stack atlas

Authors: Worker 840 (original draft, previous project instance) and
Worker 4828 (current revision, task `3931bd2c-94d1-4d23-acab-fbcd0c8074a7`).

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardAssembly`.

This internal assembly module reduces
`FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement` to a single input: a
locally finite type smooth stack atlas,
`PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas A.X.hom`, of the relative
Picard groupoid of each abelian scheme. In its final form the input is
`FiniteTypePicardStackAtlasStatement.{u}`. Via published reductions, the two
propositions `FiniteTypeFormalVersalBundleStatement.{u}` and
`CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`
together also suffice. Only these one-way implications are proved; no converse
is claimed. These inputs remain explicit hypotheses here; none of them is
proved in this module, so the module is intermediate conditional support and
does not prove the target statement.

## Abelian-scheme inputs

Let `A` be an actual abelian scheme over an arbitrary scheme `S`.

The published lemma `AbelianScheme.relativeProjection_app_isIso A T U`, from
the Library module `Langlands.AlgebraicGeometry.Picard.AbelianPicardSheafSeparated`,
states that, for every `T` over `S` and every open `U` of `T`, the projection
`T ×_S A → T` induces an isomorphism on sections over `U`. This is the
universal structure-sheaf condition `O_T ≅ (p_T)_* O_{T ×_S A}`. This module
imports that lemma and does not declare it again.

`AbelianScheme.etaleClassSheafPresheaf_isSheaf_fppf A` proves that the actual
etale sheafification of ordinary line-bundle classes,
`RelativePicard.etaleClassSheafPresheaf A.X.hom`, is a sheaf for the fppf
topology on the full slice over `S`. It applies
the published `RigidifiedLineBundle.etaleClassSheafPresheaf_isSheaf_fppf` from
the module `Langlands.AlgebraicGeometry.Picard.RigidifiedEtaleFppfClassSheaf`.
The section is the unit section `unitSection A`, with
`unitSection_comp A`, and the structure-sheaf condition is the published lemma
above.

## The conditional assembly

`finiteTypeAbelianPicardSheafAlgebraicSpace_of_atlas R A hA` takes a commutative
ring `R : Type u` of finite type over `ℤ`, an actual abelian scheme `A` over
`Spec R`, and a stack atlas `hA`. It concludes exactly the body of the target
statement for this `R` and `A`:

- the actual fppf Picard class sheaf `RelativePicard.classSheaf A.X.hom` is an
  algebraic space over `Spec R`; and
- there are a scheme `U` over `Spec R` and a transformation from its Yoneda
  presheaf to `RelativePicard.classSheafPresheaf A.X.hom` that is etale and
  surjective, with `U → Spec R` locally of finite presentation.

The proof has three steps.

1. The published `smoothAutomorphismEtaleAtlas` is applied to `A.X.hom`. Its
   fpqc stack hypothesis is the published `lineBundleFpqcStack`, its atlas
   hypothesis is `hA`, and its automorphism hypothesis is
   `AbelianScheme.hasSmoothRelativeAutomorphismSchemes A` from
   `Langlands.AbelianScheme.AffineUnitScheme`. This gives a representable
   diagonal and an etale surjective atlas, locally of finite type, of the etale
   class sheaf.
2. The published `RelativePicard.classSheaf_algebraicSpace_of_etale_atlas`
   transports both to the fppf class sheaf, using the fppf sheaf property of
   the previous section.
3. `R` is noetherian by `Algebra.FiniteType.isNoetherianRing ℤ R`, so `Spec R`
   is locally noetherian. Over a locally noetherian base, Mathlib's
   `LocallyOfFinitePresentation.iff_locallyOfFiniteType` turns local finite
   type of the atlas into local finite presentation.

`finiteTypeAbelianPicardSheafAlgebraicSpace_of_atlases` quantifies this over all
`R` and `A`. From a stack atlas for every abelian scheme over every finite-type
`ℤ`-algebra in universe `u`, it proves
`FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u}`.

`finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas h` derives the same
conclusion from `h : FiniteTypePicardStackAtlasStatement.{u}`. That statement
gives a stack atlas for every proper flat scheme over `Spec R` for each
finite-type `ℤ`-algebra `R`. It applies to `A.X` because an abelian scheme is
proper, which is a field of the structure, and smooth. Mathlib's instance
`Smooth f → Flat f` supplies flatness. The hypothesis `h` is applied directly
to the actual `A.X : Over (Spec R)`; no other scheme replaces it.

`finiteTypeAbelianPicardSheafAlgebraicSpaceOfStackAtlas` is the same
implication packaged as a single term of type
`FiniteTypePicardStackAtlasStatement.{u} →
FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u}`. It is a `def` whose
value is the theorem above (the `linter.defProp` lint is switched off for this
one declaration). It is the declaration recorded for review.

## The versal inputs

`finiteTypeAbelianPicardSheafAlgebraicSpace_of_versalInputs hF hA` derives the
target from

- `hF : FiniteTypeFormalVersalBundleStatement.{u}`: formally versal line
  bundles over complete noetherian local bases at every finite-type field point;
  and
- `hA : CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`:
  finite-order etale approximation into the completion of every maximal
  localization of a finite-type `ℤ`-algebra.

It composes three published Library results with the theorem above:
`versalAlgebraization_of_etaleApproximation hA` gives
`VersalAlgebraizationStatement.{u}`; the published proof
`picardOpennessOfVersality` gives `PicardOpennessOfVersalityStatement.{u}`;
and `PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` combines `hF`
with these two to give `FiniteTypePicardStackAtlasStatement.{u}`. The final
step is `finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas`.

## Scope and provenance

This is internal support built from published Library results, the helper
module `Langlands.AbelianScheme.AffineUnitScheme` and Mathlib, with no new
external assertion. It records the final step of the corrected Artin route
described in the target statement's Markdown (Artin 1974, Appendix item 2):
smooth automorphism groups, an algebraic Picard stack with a smooth atlas, and
the etale sheaf of isomorphism classes, compared with the Library's fppf class
sheaf. In Artin's notation (printed p. 187) the Picard stack `F` is presented
by an algebraic stack `P^1 ⇒ P^0`: `P^0` is the object atlas and `P^1` the
scheme of arrows. With `R = P^1 ×_(P^0 × P^0) P^1`, smoothness of the
automorphism groups makes `R` a smooth equivalence relation on `P^1`. Its
quotient `bar(P^1) = P^1/R` is an algebraic space, and `bar(P^1) ⇒ P^0` is the
equivalence relation on `P^0` that defines the Picard sheaf `Pic X/S`. Thus
`Pic X/S` is the quotient of `P^0` by `bar(P^1)`, not `P^1/R` itself. The Lean
proof follows this route through the published adapters
`smoothAutomorphismEtaleAtlas` and
`RelativePicard.classSheaf_algebraicSpace_of_etale_atlas`; it does not
formalize Artin's quotient construction. The stack-atlas hypothesis, and likewise
`FiniteTypePicardStackAtlasStatement` and the two versal inputs, are the stack
input of that route. They are not proved here, so these conditional theorems do
not by themselves prove the target statement. All test schemes over the base
are retained, and no premise on `R` or `A` beyond the target's own is
introduced.
