# Finite-stage categories of actual Picard families

This internal construction, by Worker 149, combines the published actual-family
descent theorem with the canonical finite-enlargement Isom-section colimit.
It constructs a category whose objects live at finite subalgebra stages and
whose morphisms are Type colimits of actual Isom sections. Ordinary extension
to the whole algebra is an equivalence of categories.

All rings, schemes and algebras have the arbitrary universe `u` used in the
atlas target. Let `R → A` be an algebra of commutative rings and let
`f : X → Spec R`. The object definitions require no geometric hypotheses.
The category, evaluation functor and equivalence require `f` proper, flat
and locally of finite presentation.

## Objects and actual extension

`AffineStageFamily f` has fields:

- `stage : AffineAlgebraStage R A`, a subalgebra `B ⊆ A` with `B.FG`;
- `family`, an object of the actual Picard groupoid on `X ×[Spec R] Spec B`.

Here the Picard groupoid is the core of the category of line bundles. Thus its
objects and arrows retain the actual line bundles and their isomorphisms.
`evaluation` is ordinary pullback along the inclusion-induced affine arrow
`affineSubalgebraMap B`.

For two objects `L,M`, `commonStage` is the finitely generated subalgebra
`D = B ⊔ C`. `atStage` uses the actual inclusion-induced arrow
`affineAlgebraStageMap` to restrict each family to `D`.
`evaluationIso` identifies direct extension of a family from its original
stage to `A` with extension first to `D` and then to `A`. It is the component
of the ordinary pseudofunctor's `mapComp'` comparison. The equation needed
to apply that comparison is `affineAlgebraStageMap_restrict`.

## Morphisms as finite-stage colimits

`homPresheaf L M` is the coherent actual Isom presheaf of the two restricted
families on the iterated slice over `Spec D`. It uses
`affineEnlargementIsomPresheaf`, including its universe lift.
`homDiagram L M` restricts this presheaf to the canonical finite `R`-subalgebra
stages `E ⊆ A` containing `D`, with their actual inclusion-induced maps.

The type `Hom L M` is the categorical Type colimit of `homDiagram L M`.
In particular, it is defined before, and independently of, the category of
whole-algebra arrows. `ofSection` inserts a specified section at a finite
enlargement into this colimit. `exists_section` proves every colimit morphism
has such a representative, by joint surjectivity of a Type colimit's legs.

`wholeHomEquiv` identifies the whole-algebra value of the coherent Isom
presheaf with arrows between the directly evaluated original families.
It removes the universe lift and uses `Iso.homCongr` with the inverse
`evaluationIso` comparisons. Thus a whole-base section `φ` is sent to
`eL.hom ≫ φ.down ≫ eM.inv`, where `eL,eM` are those ordinary pullback
comparisons.

`homEquiv` first applies the unique isomorphism between the abstract Type
colimit and the canonical whole-algebra cocone, using the published
`affineEnlargementIsomSectionsIsColimit`. It then applies `wholeHomEquiv`.
Properness, flatness and local finite presentation discharge the hypotheses
of that published Isom-section colimit.

`homEquiv_ι` checks its action on every canonical colimit leg.
`evaluationFunctor_map_ofSection` expresses the same calculation as a
functor equation: a finite-stage section maps by its canonical presheaf
restriction to `A`, followed by `wholeHomEquiv`. These equations retain
the specified finite-stage section and the pullback coherence.

## Category and equivalence

Identity and composition on the genuine colimit Hom types are transported
through the proved `homEquiv`. Injectivity of that equivalence proves
the category laws. `evaluationFunctor` sends objects by ordinary extension
and morphisms by `homEquiv`; the inverse identities of the equivalence
prove its functor laws and `fullyFaithfulEvaluation`.

For essential surjectivity, `exists_affineFamily_subalgebra` descends any
actual line bundle on the whole-algebra fibre product to a finitely
generated `R`-subalgebra. The actual groupoid isomorphism supplied by that
theorem witnesses membership in the essential image. Properness supplies
the quasi-compactness and quasi-separatedness used in object descent.
Fullness, faithfulness and essential surjectivity give `equivalence`.
The final groupoid structure is transported through the fully faithful
evaluation functor from the actual target groupoid.

## Provenance and scope

This is a derived internal construction from the Library modules
`AffineEnlargementSections` and `AffineFamilyDescent`, and Mathlib's ordinary
pseudofunctor comparisons, categorical Type colimits, fully faithful functors
and equivalence criterion. No external source theorem is introduced.

The result is the stated category comparison for finitely generated
subalgebras of an actual algebra `A`. A general filtered-ring diagram,
its pseudocolimit universal property, compatibility with changes of the
whole algebra, and a smooth scheme atlas are further obligations.
This module does not assert `FieldPicardStackAtlasStatement`.
