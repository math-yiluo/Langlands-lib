# Full rigidified Picard representability for smooth proper pointed schemes: proof

Module: `Langlands.AlgebraicGeometry.Picard.SmoothProperRigidifiedPicardRepresentabilityProof`.

The theorem
`Langlands.AlgebraicGeometry.Picard.smoothProperRigidifiedPicardRepresentability`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.SmoothProperRigidifiedPicardRepresentabilityStatement.{u}`
for every universe `u`. Its type is exactly that proposition. The statement
module and its Markdown are imported unchanged. The theorem has no hypotheses.
The kernel reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is proved

Let `K : Type u` be any field and let `X : Over (Spec (CommRingCat.of K))`
have a smooth, proper and geometrically connected structure morphism. Let
`ε : Spec (CommRingCat.of K) ⟶ X.left` be an actual section with
`ε ≫ X.hom = 𝟙 _`. Then there are a scheme `P` over `K` and an actual
rigidified line bundle `L : RigidifiedLineBundle.relative X.hom ε section_eq P`
such that `IsSeparated P.hom`, `LocallyOfFiniteType P.hom` and
`RigidifiedLineBundle.IsUniversal X.hom ε section_eq L` hold. By definition,
`IsUniversal` says that the canonical pullback classifying map of `L` is
bijective for every test scheme `T` over `K`. The tests include nonreduced and
non-quasi-compact schemes.

The field is arbitrary: it may be imperfect, need not be algebraically closed,
and can have any characteristic. The final theorem assumes no projectivity,
ampleness, group structure, Picard-zero condition, representability,
universal family, structure-sheaf condition or comparison. Each input below is
either a published theorem with no hypotheses or is derived inside the proof.

## Declarations

### `universalStructureSheafOfSmoothProper`

Let `f : X ⟶ S` be smooth, proper and geometrically connected over any base
scheme `S`. For every `T : Over S` and every open `U` of `T.left`, the theorem
proves `IsIso (((relativeProjection f).app T).app U)`.

The proof applies the published theorem
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` (module
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`) to the
base-changed projection `pullback.fst T.hom f`. Mathlib's base-change instances
show that this projection is smooth, proper and geometrically connected. The
projection `(relativeProjection f).app T` is `pullback.fst T.hom f` by
definition. So the canonical map is an isomorphism on every open of every test
scheme, not only over the field.

### `universalBundleOfPicardComparison`

This is a general categorical step. Its inputs are a presheaf
`F : (Over S)ᵒᵖ ⥤ Type (u + 1)`, a natural representation
`r : F.RepresentableBy P`, and a natural isomorphism `comparison` from the
rigidified class presheaf
`RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq`
to `F`. The proof moves the representation to the class presheaf with Mathlib's
`Functor.RepresentableBy.ofIso` along `comparison.symm`.

It then applies the published
`RigidifiedLineBundle.representationUniversalBundle` (module
`RigidifiedRepresentationUniversalBundleProof`). That theorem takes the class
corresponding to `𝟙 P` and chooses an actual representative bundle `L`. By
naturality of the representation, the canonical pullback classifying map of `L`
at each `T` equals the representation's bijection `T ⟶ P ≃ classes over T`. So
`L` satisfies `IsUniversal`. The helper keeps the bundle and the universality
and drops the extra equation.

### `canonicalPicardComparisonIso` and `canonicalPicardComparisonIso_hom`

Given an `IsIso` instance for the published canonical transformation
`RigidifiedLineBundle.toPicardSheaf f ε section_eq`,
`canonicalPicardComparisonIso` is `asIso` of that transformation followed by
the published `RelativePicard.forgetSheafIso f`. Its target is
`RelativePicard.classSheafPresheaf f`, the actual set-valued fppf
sheafification of the ordinary Picard class presheaf.

The simp lemma `canonicalPicardComparisonIso_hom` uses the published
`RigidifiedLineBundle.toPicardSheaf_forgetSheafIso_hom` to show that the
forward map is `RigidifiedLineBundle.toClassPicardSheaf f ε section_eq`. That
map forgets the rigidification and takes the sheafification image of the
underlying line bundle. So the comparison used below is the canonical
forget-rigidification and sheafification map, with its naturality in pullbacks.
It is not an arbitrary isomorphism. The final theorem does not use this lemma,
because `IsUniversal` refers only to the canonical classifying map of `L`. The
lemma is kept to record that the comparison is canonical.

### `smoothProperRigidifiedPicardRepresentability`

The proof introduces `K`, `X`, the three hypotheses, `ε` and `section_eq`. It
makes the hypotheses available as instances. Then it takes three steps.

1. **Representability of the fppf Picard sheaf.** The published reduction
   `fieldPicardSheafRepresentability_of_stackAtlas` (module
   `FieldPicardSheafRepresentabilityReduction`) is applied to the published
   theorem `fieldPicardStackAtlas : FieldPicardStackAtlasStatement.{u}` (module
   `FieldPicardStackAtlasProof`). The result is
   `FieldPicardSheafRepresentabilityStatement.{u}`. Applying it to `K`, `X` and
   properness gives `P` with `IsSeparated P.hom`, `LocallyOfFiniteType P.hom`
   and a natural representation
   `r : (RelativePicard.classSheafPresheaf X.hom).RepresentableBy P`. Only
   properness is used in this step.
2. **Canonical comparison.** The published theorem `rigidifiedFppfComparison`
   (module `RigidifiedFppfComparisonProof`) is applied to `X.hom` and the
   actual section. Its hypotheses are derived as follows.
   Quasi-compactness and quasi-separatedness come from properness by instance
   inference. The universal structure-sheaf condition on every open of every
   test scheme is `universalStructureSheafOfSmoothProper X.hom`. The result is
   an `IsIso` instance for `RigidifiedLineBundle.toPicardSheaf X.hom ε section_eq`.
3. **Universal bundle.** `universalBundleOfPicardComparison` is applied with
   `F = RelativePicard.classSheafPresheaf X.hom`, the representation `r`, and
   `canonicalPicardComparisonIso X.hom ε section_eq`. This gives an actual
   bundle `L` over `P` with `IsUniversal`.

The witness is `⟨P, L, hsep, hlft, hL⟩`. Separatedness and local finite type
are those of the representing scheme from step 1.

## Upstream proofs used

All of the following are published Library theorems with no hypotheses:
`fieldPicardStackAtlas`, `rigidifiedFppfComparison`,
`smoothProperConnectedGlobalFunctions` and
`RigidifiedLineBundle.representationUniversalBundle`. The theorem
`fieldPicardSheafRepresentability_of_stackAtlas` is a published reduction, and
it is applied here to a published proof. This module applies the reduction
directly. It does not import a separate proof module of
`FieldPicardSheafRepresentabilityStatement` or declare a theorem with that type.

## Relation to the source

The route is the one in the target's paired Markdown. Edixhoven, van der Geer
and Moonen, *Abelian Varieties*, preliminary draft (registered
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter VI (6.2) and
(6.3)(iii), printed pp.88–89 (PDF pp.92–93), give this route. Under condition
(*), the rigidified functor agrees with the fppf Picard sheaf. That sheaf is
representable by a separated scheme locally of finite type over the field, and
the representing scheme carries a universal Poincaré bundle. Condition (*) is
supplied by the universal global-functions theorem (Stacks Project Tags 056T and
0E0L, as recorded in the target Markdown) and by the actual section. The
representability input is formalized differently from the cited attribution to
Murre and Oort: the published `fieldPicardStackAtlas` builds a Picard stack
atlas with Artin's criteria on a finite-type model, as its own Markdown explains.
This module adds no new geometry. It only composes those published results
through the categorical step above.

## Development check

A `lean_check` run on 16 November 2026 over Library base
`79158f8d72db4ee20941c2e6adc70b6d5252e039` reports a successful build with no
errors or warnings. It inspects
`smoothProperRigidifiedPicardRepresentability`: a theorem with universe
parameter `u` and axioms `propext`, `Classical.choice` and `Quot.sound`. This
is a development check.
