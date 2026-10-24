# Scalar restriction, group restriction and reindexing

This module constructs natural interchange isomorphisms between coefficient
scalar restriction, restriction of the acting group, and reindexing of
compatible equivariant small-etale coefficient diagrams. It also proves
compatibility of the existing ordinary global-section comparisons with these
operations.

## Provenance and inputs

This is an internal construction from the published
`EtaleScalarRestriction`, `EtaleScalarDiagram`,
`EtaleActionRestriction`, `EtaleEquivariantCoefficientReindex`, and
`EtaleEquivariantCoefficientRestriction` modules. No external theorem is
transcribed. Scalar restriction postcomposes section modules with Mathlib's
`ModuleCat.restrictScalars`; group restriction selects the original
equivariant structure map at the image of a group element; reindexing selects
the original vertices and arrows. These actual constructions are used to
derive the interchanges, rather than taking the desired comparison maps or
their compatibility as inputs.

The parameters are commutative rings `R, A : Type u`, a ring homomorphism
`φ : R →+* A`, groups `G : Type t` and `H : Type t'`, and a group homomorphism
`ψ : H →* G`. The schemes and section-module carriers also use universe `u`.
No injectivity, surjectivity or flatness hypothesis is imposed on `φ` or `ψ`.
The groups carry no required topology.

For the single-space construction, `X : Scheme.{u}` and
`ρ : G →* (Aut X)ᵐᵒᵖ` are supplied. The opposite automorphism convention is
the existing one: `aut ρ (g * h)` is `aut ρ g` followed by `aut ρ h`.
The coefficients are actual `EquivariantSheaf A ρ` objects on the small-etale
site of `X`, with the geometric equivariance laws already proved as part of
those objects.

For diagrams, `J : Type v` has morphisms in universe `w` and
`S : J ⥤ Scheme.{u}ᵒᵖ` is supplied, with each unop scheme arrow etale. Thus
`a : i ⟶ j` gives `f_a : X_j ⟶ X_i`, where `X_i = (S.obj i).unop`.
The supplied actions `ρ i` satisfy the geometric equivariance equations

```text
f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a.
```

An `EquivariantCoefficientDiagram A S ρ hρ` supplies equivariant sheaves at
the vertices and compatible geometric pullback transitions, with their
identity and composition laws. For reindexing, `I : Type v'` has morphisms
in universe `w'`, and `F : I ⥤ J` is arbitrary.

## Group and scalar restriction of a sheaf

`scalarRestrictionGroupIso φ ψ ρ` compares the functors

```text
scalarRestrictionFunctor φ ρ ⋙ restrictionFunctor R ρ ψ
  ≅ restrictionFunctor A ρ ψ ⋙ scalarRestrictionFunctor φ (ρ.comp ψ).
```

In either order the resulting sheaf is the original sheaf with its scalar
action restricted by `φ`. Its structure map for `h : H` is the scalar
restriction of the original structure map at `ψ h`. On morphisms both
orders restrict the same underlying sheaf map. The two functors are
definitionally equal, so the isomorphism is `Iso.refl`. The lemmas
`scalarRestrictionGroupIso_hom_app_hom` and
`scalarRestrictionGroupIso_inv_app_hom` identify both underlying sheaf maps
as identities.

`scalarRestrictionGroup_sections` proves equality of the following two
composite section comparisons, starting with the sections obtained by
restricting scalars and then the group:

1. Apply the group section comparison, followed by the group restriction
   of the scalar section comparison.
2. Apply sections to the sheaf interchange, then the scalar section
   comparison for the group-restricted sheaf, followed by scalar restriction
   of the group section comparison.

Both have target the original ordinary section action with scalars
restricted along `φ` and group action restricted along `ψ`. The two
orders of restriction on the target module actions are definitionally
equal. The proof uses extensionality for action morphisms. The group
comparison and sheaf interchange have identity underlying maps; the
section and scalar functors preserve those identities. After these
simplifications both sides are the same ordinary scalar section comparison.
In particular, the argument does not assume that the scalar section
comparison itself is an identity.

## Interchange on compatible diagrams

In namespace `EquivariantCoefficientDiagram`,
`restrictScalarsGroupIso φ ψ` compares

```text
restrictScalarsFunctor φ ⋙ restrictGroupFunctor ψ
  ≅ restrictGroupFunctor ψ ⋙ restrictScalarsFunctor φ.
```

Both functors start at `EquivariantCoefficientDiagram A S ρ hρ` and end at
the `R`-coefficient diagram category with actions `(ρ i).comp ψ` and
equivariance equation `hρ a (ψ h)`. Their object, transition and morphism
data are definitionally equal; the already proved intrinsic laws are
proposition-valued fields. Consequently `Iso.refl` supplies this natural
isomorphism, including compatibility with transitions.

The lemmas `restrictScalarsGroupIso_hom_app_app` and
`restrictScalarsGroupIso_inv_app_app` identify its forward and inverse
component at vertex `i` with the corresponding single-sheaf interchange.

`restrictScalarsGroup_sections` is the whole-diagram version of the section
compatibility above. Its first route uses `restrictGroupSectionsIso` and
postcomposes `restrictScalarsSectionsIso` by the action-restriction functor.
Its second route applies `sectionsFunctor` to the coefficient-diagram
interchange, then uses the scalar section comparison and the scalar
restriction of the group section comparison. Equality of these natural
transformations follows by evaluating at every vertex and applying
`scalarRestrictionGroup_sections`.

## Reindexing and scalar restriction

`reindexRestrictScalarsIso φ F` compares

```text
reindexFunctor F ⋙ restrictScalarsFunctor φ
  ≅ restrictScalarsFunctor φ ⋙ reindexFunctor F.
```

The source is the `A`-coefficient diagram category over `S`. The target is
the `R`-coefficient diagram category over `F ⋙ S`, with actions
`ρ (F.obj i)` and equivariance equations `hρ (F.map a) g`. Both orders
select `D.obj (F.obj i)` at a vertex and `D.map (F.map a)` for a transition
and apply the same published scalar construction. They also give the same
component on coefficient morphisms. This comparison is again `Iso.refl`.

The lemmas `reindex_restrictScalarsSectionsIso_hom_app` and
`reindex_restrictScalarsSectionsIso_inv_app` identify the forward and inverse
scalar section comparison at `i` after reindexing with the original
comparison at `F.obj i`. The whole natural transformations are identified
by `reindex_restrictScalarsSectionsIso_hom` and
`reindex_restrictScalarsSectionsIso_inv`:

```text
(restrictScalarsSectionsIso φ (reindex F D)).hom
  = Functor.whiskerLeft F (restrictScalarsSectionsIso φ D).hom,
```

and likewise for `.inv`. These equalities follow directly from the
vertexwise definition of the published scalar section comparison.
The source and target diagrams in these equalities are definitionally
identified by the same reindexing formulas.

## Scope

The constructions concern ordinary small-etale coefficient sheaves and
ordinary global sections with algebraic group actions. The arbitrary index
category allows suitably oriented inverse diagrams, but this module does
not construct their limits or compare scalar restriction with those
limits. It makes no higher-derived scalar comparison, injective-preservation,
tensor-extension, ideal-reduction, ring-composition coherence, smoothness,
analytic-site, compact-support or Harris-specialization claim.
