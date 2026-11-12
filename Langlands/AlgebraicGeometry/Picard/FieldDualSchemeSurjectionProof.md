# Surjectivity onto the chosen dual parameter scheme over every field

`Langlands.AbelianScheme.fieldDualSchemeSurjection` proves exactly the
published `Langlands.AbelianScheme.FieldDualSchemeSurjectionStatement.{u}`.
For every field `k : Type u`, every
`A : AbelianScheme (Spec (CommRingCat.of k))`, and every `hA : HasDualScheme A`,
it constructs a morphism `f : A.X ⟶ dualScheme A hA` in `Over (Spec k)`
whose underlying scheme morphism is surjective. The theorem has no additional
outer hypotheses and is universe-polymorphic.

## Choosing the actual Mumford map

The proof supplies arbitrary-field ample existence using the published
`Langlands.GroupScheme.fieldAmpleExistence`, imported from
`Langlands.AbelianScheme.FieldAmpleExistenceProof`, at its complete type
`GroupScheme.FieldAmpleExistenceStatement.{u}`. Apply it to `A.toGrp` with
the smoothness, properness and geometric connectedness of `A`.

The helper `exists_rigidified_ample_of_fieldAmpleExistence` restricts the
resulting ample bundle along the unit and uses the published
`fieldLineBundleTriviality` to trivialize that restriction. The inverse
trivialization equips the original bundle with a rigidification. Its carrier
remains definitionally the same ample bundle, so no ampleness transport is
needed here. The published
`LineBundle.exists_tensorObj_iso_structureSheaf` supplies an actual ordinary
inverse bundle and evaluation isomorphism.

The actual `mumfordSchemeMap` classifies the resulting rigidified Mumford
family in the chosen `dualScheme A hA`. The final proof supplies its
pullback-tensor premise with the published
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`, imported from
`Langlands.AlgebraicGeometry.Modules.PullbackTensorProof`. It supplies
geometric Picard-zero membership with the published
`Langlands.AbelianScheme.mumfordBundlePicardZero`, imported from
`Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroProof`.
The latter has exactly `MumfordBundlePicardZeroStatement.{u}` as its type:
it uses the same comparison proof, actual rigidified bundle, ordinary inverse
and supplied evaluation, and proves geometric translation invariance of the
constructed family. Neither statement is assumed as additional data.

## Lifting points of the chosen parameter scheme

Fix an algebraically closed field `K : Type u`, a base map
`b : Spec K ⟶ Spec k`, and a point `p : Over.mk b ⟶ dualScheme A hA`.
Pull the original ample bundle and its chosen inverse back along the first
projection of the actual base change of `A`. `pullbackTensorEvaluation`
transports the evaluation isomorphism. The published
`Langlands.AlgebraicGeometry.Picard.fieldBaseChangeAmple`, imported from
`Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleProof`, proves
ampleness of that pulled-back bundle.

The helper `poincare_point_translation_invariant` uses the published
`picardZeroPullback` to pull the actual Poincare family back along `p`.
The published `isTranslationInvariant_of_isGeometricallyPicardZero` then
gives ordinary translation invariance of its underlying bundle on the
base-changed abelian scheme.

The proof supplies the published
`Langlands.AbelianScheme.algClosedFieldTranslationDifferenceLifting`,
imported from
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof`,
at its complete type `AlgClosedFieldTranslationDifferenceLiftingStatement.{u}`.
Apply it with the same pullback-tensor proof, pulled-back ample bundle,
actual inverse and evaluation, and the translation-invariant bundle obtained
from `p`. It constructs a section whose translation difference is actually
isomorphic to that bundle.

`exists_point_of_baseChangeSection` composes this section with the first
pullback projection to obtain a point of the original abelian scheme over
the test field. The pullback equation and section equation prove its
compatibility with the original base.

The published `Langlands.AbelianScheme.fieldMumfordPointComparison`,
imported from
`Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof`, converts
the ordinary translation-difference isomorphism into an isomorphism of the
actual rigidified parameter pullbacks of the Mumford and Poincare families.
Its type is exactly `FieldMumfordPointComparisonStatement.{u}`; the proof
applies it to the constructed section, its projection, the pullback equation,
and the pulled-back Poincare family.

The helper `mumford_point_eq_of_iso` uses `mumfordSchemeMap_points` and
`Quotient.sound` to identify the associated rigidified classes. The published
`dualPointClass_injective`, applied with `picardZeroPullback`, turns that
class equality into equality of the parameter maps in the chosen scheme.
Thus every such `p` lifts through the constructed Mumford map.
`mumfordSchemeMap_surjective_of_rigidified_lifts` packages this argument.

## From geometric points to surjectivity

The helper `surjective_of_algClosed_point_lifting` applies to any morphism in
`Over S`. Given an underlying point `y` of its target, take the algebraic
closure of the actual residue field at `y`. Compose its spectrum map with
`Y.fromSpecResidueField y` and view it as a point over `S`. A lift of that
point, evaluated at the unique point of the spectrum of the algebraic
closure, maps to `y`. `Scheme.fromSpecResidueField_apply` proves the last
equality.

All test fields remain in universe `u`. This argument imposes no finite-type
or separatedness assumption on the chosen parameter scheme and no
perfection assumption on the original field. Surjectivity here is
Mathlib's `AlgebraicGeometry.Surjective`, namely surjectivity on underlying
points. No compatibility with a group law on the target is asserted.

## Provenance and authorship

This is an internal deduction from the published actual-family and
classification results and Mathlib's residue-field and algebraic-closure
constructions. It preserves `HasDualScheme`, the chosen `dualScheme`, its
Poincare family, and the geometric translation-invariance predicate. It
uses no downstream chosen-dual geometry theorem.

The geometric motivation is the registered Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, preliminary draft,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88/PDF p.92, concerns the actual rigidified
universal property. Chapter VI section 3 and Theorem (6.18), printed
pp.95–96/PDF pp.99–100, construct the ample Mumford map and prove the
isogeny onto the source's Picard identity component. Proposition (7.21)
and Corollary (7.22), printed pp.105–106/PDF pp.109–110, supply the
translation-invariant point description. These passages were read during
development. The bounded errata check found no book-specific errata file
or author-page link; it does not establish a global absence of corrections.

The source's Picard identity component is not by itself identified with the
Library's chosen parameter scheme. The implemented rigidified-family
comparisons and injectivity of its classifying map supply the needed
identification of points. The imported lifting proof owns the substantial
sheaf and cohomology argument behind Proposition (7.21); this module uses
its published theorem rather than reproducing that argument.

Worker 420 authored the carried conditional assembly and its original
explanation. Worker 1386 restored and checked it after the project transfer
and completed the unconditional assembly by supplying the published
Mumford Picard-zero, ordinary translation-difference lifting and
arbitrary-field ample-existence proofs. The imported results retain their
authorship in their own paired explanations.
