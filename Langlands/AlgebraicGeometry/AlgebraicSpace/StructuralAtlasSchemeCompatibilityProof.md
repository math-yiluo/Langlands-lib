# Structural atlas geometry agrees with scheme geometry on actual schemes (proof)

This module proves the published proposition
`StructuralAtlasSchemeCompatibilityStatement` from
`Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityStatement`.
The theorem `structuralAtlasSchemeCompatibility` has exactly the type
`StructuralAtlasSchemeCompatibilityStatement.{u}`. It therefore covers every
scheme `S : Scheme.{u}`, every scheme `U : Over S` and an arbitrary universe
`u`. For each of smoothness, local finite presentation and local finite type,
the published one-atlas predicate of the embedded scheme
`(schemeToSpace S).obj U` is equivalent to the Mathlib property of the
actual structure morphism `U.hom : U.left ⟶ S`.

The three equivalences are proved separately, and none uses another. In
particular, the local finite presentation and local finite type branches use
no smoothness. The proof adds no affineness, reducedness, noetherianity,
quasi-separatedness, quasi-compactness, dimension, finite type or
projectivity hypothesis. It keeps the published predicates, the actual
scheme embedding, the published `IsEtale` and geometric `IsSurjective`, and
Mathlib's `Smooth`, `LocallyOfFinitePresentation` and `LocallyOfFiniteType`.

## Imports

- `Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityStatement`,
  the target statement. Through it the module gets
  `StructuralAtlasGeometry` and `Basic`.
- `Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof`, for
  `smoothEtaleSourceDescent : SmoothEtaleSourceDescentStatement.{u}`. That
  statement says: if `p : W ⟶ X` is etale and surjective and `p ≫ g` is
  smooth, then `g` is smooth.
- `Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent`,
  for `locallyOfFinitePresentation_of_surjective_flat_comp`. If `f` is
  surjective, flat and locally of finite presentation, and `f ≫ g` is locally
  of finite presentation, then `g` is locally of finite presentation. The four
  hypotheses are typeclass arguments.
- `Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof`,
  for `locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp :
  LocallyOfFiniteTypeSourceDescentStatement.{u}`. It has the same
  hypotheses on `f` as explicit arguments, and concludes local finite type of
  `g` from local finite type of `f ≫ g`.

All three descent results are published proofs. They are imported by Lean
name and are not hypotheses of this module.

## Declarations

All declarations are in namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`,
with `S : Scheme.{u}` implicit.

- `exists_etale_surjective_of_represented_atlas`. Let `W U : Over S` and let
  `a : (schemeYoneda S).obj W ⟶ (schemeYoneda S).obj U` satisfy `IsEtale a`
  and `IsSurjective a`. Then there is `f : W ⟶ U` such that `f.left` is etale
  and surjective. The functor `schemeYoneda S` is Mathlib's `uliftYoneda`,
  which is full, so `Functor.map_surjective` gives `f` with Yoneda image `a`.
  The published `IsEtale` is the relative property
  `(MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
  (schemeYoneda S)`, and `IsSurjective` is the same with `Surjective`.
  Mathlib's `MorphismProperty.of_relative_map` takes such a relative property
  of `F.map f` and returns `P f`, by testing it on the trivial pullback square
  of `F.map f` along the identity. For the inverse image along `Over.forget S`,
  `P f` is `Etale f.left`, respectively `Surjective f.left`.
- `smoothOverBase_schemeToSpace_iff U`. This proves
  `SmoothOverBase ((schemeToSpace S).obj U) ↔ Smooth U.hom`. The backward
  direction is the published identity-atlas lemma `SmoothOverBase.of_scheme U`.
  For the forward direction, `SmoothOverBase.exists_atlas` gives an atlas
  `W : Over S` and `a : (schemeYoneda S).obj W ⟶ ((schemeToSpace S).obj U).presheaf`
  with `IsEtale a`, `IsSurjective a` and `Smooth W.hom`. The presheaf of
  `(schemeToSpace S).obj U` is definitionally `(schemeYoneda S).obj U`, so
  the previous lemma applies to `a` and gives `f`. Mathlib's `Over.w f` is
  `f.left ≫ U.hom = W.hom`. Rewriting with it turns `Smooth W.hom` into
  `Smooth (f.left ≫ U.hom)`. Then `smoothEtaleSourceDescent`, applied to
  `p := f.left` and `g := U.hom`, gives `Smooth U.hom`.
- `locallyOfFinitePresentationOverBase_schemeToSpace_iff U`. This is the
  same argument for local finite presentation. The backward direction is
  `LocallyOfFinitePresentationOverBase.of_scheme U`. In the forward direction,
  the rewritten atlas property `LocallyOfFinitePresentation (f.left ≫ U.hom)`
  is a local instance, and so is the hypothesis `Surjective f.left`.
  Instance search derives flatness and local finite presentation of `f.left`
  from `Etale f.left`, using the pinned Mathlib instances for etale
  morphisms. `locallyOfFinitePresentation_of_surjective_flat_comp f.left U.hom`
  then gives `LocallyOfFinitePresentation U.hom`.
- `locallyOfFiniteTypeOverBase_schemeToSpace_iff U`. This is the same
  argument for local finite type. The backward direction is
  `LocallyOfFiniteTypeOverBase.of_scheme U`. In the forward direction, the
  LFT descent result is applied to `f.left` and `U.hom`. Its arguments are
  `Surjective f.left`, flatness and local finite presentation of `f.left`
  (found by instance search from `Etale f.left`), and
  `LocallyOfFiniteType (f.left ≫ U.hom)`, obtained by rewriting with
  `Over.w f`.
- `structuralAtlasSchemeCompatibility`. Given `S` and `U`, the theorem pairs
  the three lemmas above into the required conjunction.

The converse directions use only the atlas that the predicate supplies. They
do not prove atlas independence or show that every atlas has the property.

## Checks

The development check compiles the module with zero errors and zero
warnings. The theorem has the single universe parameter `u` and uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and scope

The proved proposition is internal, derived compatibility between the
Library's chart predicates, its scheme embedding and Mathlib's scheme
properties. Its statement Markdown traces it to the representable case of
Stacks Project Lemma 67.22.1 (Tag 03MJ) and the one-atlas criteria in Lemmas
67.37.4(6) (Tag 03ZB) and 67.28.4(6) (Tag 03XO). The Lean route above
combines Yoneda reflection with the published scheme descent results, and
follows the source-level route sketched in the task context. It is not a
transcription of a cited proof.

This module concerns only the three named properties on actual schemes. It
does not prove general atlas independence, compatibility for arbitrary
properties, or anything about properness. It constructs no Picard
representer, group scheme, universal family or actual-family comparison.

## Authorship

Worker 840 wrote the Lean proof and this Markdown.
