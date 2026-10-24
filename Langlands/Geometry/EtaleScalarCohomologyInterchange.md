# Scalar and group restriction in degree-zero etale cohomology

This module constructs natural comparisons for degree-zero cohomology after
both coefficient scalar restriction and restriction of the acting group.
It treats geometric equivariant small-etale sheaves and compatible
varying-scheme coefficient diagrams. The canonical scalar comparisons commute
with group restriction and with reindexing of diagrams.

## Provenance

This is an internal construction from published project definitions.
`EtaleScalarCohomologyZero` supplies the canonical degree-zero scalar
comparisons, transported from ordinary sections. `EtaleActionRestriction`
and `EtaleEquivariantCoefficientRestriction` supply the group restriction
comparisons on cohomology. `EtaleScalarInterchange` provides coefficient
interchange isomorphisms and the reindexing constructions.

The present natural isomorphisms are composites and whiskerings of those
published maps, using the categorical associators to match their domains.
The new compatibility equations are proved from the actual component maps;
they are not assumptions. No external theorem is transcribed, and no
unpublished scalar-cohomology coherence construction is used.

## Inputs and conventions

The coefficient rings `R, A : Type u` are commutative and
`φ : R →+* A` is arbitrary. Schemes and module carriers use the same
universe `u`. The groups `G : Type t` and `H : Type t'` have an arbitrary
homomorphism `ψ : H →* G`. Neither map needs to be injective or
surjective, and no topology or flatness hypothesis is imposed.

For a single scheme `X : Scheme.{u}`, the geometric action is supplied as
`ρ : G →* (Aut X)ᵐᵒᵖ`. Thus the automorphism of `g * h` is the
categorical composite of the automorphism of `g` followed by that of `h`.
An `EquivariantSheaf A ρ` is an actual small-etale module sheaf with its
geometric equivariance structure.

For diagrams, `J : Type v` has morphisms in universe `w`,
`S : J ⥤ Scheme.{u}ᵒᵖ`, and every unop scheme arrow is etale.
Writing `Xᵢ = (S.obj i).unop`, an arrow `a : i ⟶ j` gives
`fₐ : Xⱼ ⟶ Xᵢ`. The vertex actions `ρ i` satisfy

```text
fₐ ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ fₐ.
```

An `EquivariantCoefficientDiagram A S ρ hρ` supplies the vertex sheaves
and equivariant pullback transition maps with their identity and composition
laws. Reindexing uses an arbitrary functor `F : I ⥤ J`, with
`I : Type v'` and morphisms in universe `w'`.

## Simultaneous comparison on equivariant sheaves

Write `Tφ` for scalar restriction on coefficient sheaves, `U_R` for
group restriction from `G` to `H` on `R`-coefficient sheaves,
`H_R⁰` for the appropriate cohomology action functor, `rφ` for scalar
restriction on module actions, and `g_R` for group restriction on
`R`-module actions. The published canonical maps are

```text
κφ(F) : H_R⁰(Tφ F) ⟶ rφ(H_A⁰ F)
γ_R(E) : H_R⁰(U_R E) ⟶ g_R(H_R⁰ E).
```

The construction `scalarRestrictionGroupCohomologyZeroFunctorIso`
is the natural isomorphism

```text
Tφ ⋙ U_R ⋙ H_R⁰  ≅  H_A⁰ ⋙ rφ ⋙ g_R.
```

It first whiskers the group cohomology comparison by `Tφ`, uses the
inverse associator, whiskers the scalar comparison by `g_R`, and
uses the associator on the target. Its `_hom_app` lemma states that
the component at `F` is

```text
γ_R(Tφ F) ≫ g_R.map (κφ(F)).
```

The component proof unfolds this composite and removes the identity maps
of the associators.

The coefficient interchange `t(F)` from `scalarRestrictionGroupIso`
has type `U_R(Tφ F) ⟶ Tφ(U_A F)`.
The theorem `scalarRestrictionGroup_cohomologyZero` proves

```text
γ_R(Tφ F) ≫ g_R.map (κφ(F))
  =
H_R⁰.map (t(F)) ≫ κφ(U_A F) ≫ rφ.map (γ_A(F)).
```

The scalar restriction in the final term acts on `H`-actions; that
in the left-hand term acts on `G`-actions before group restriction.
The target module actions in these two orders are definitionally equal.
Both paths therefore have the same source and target, including their
`H`-equivariance.

The implemented proof uses extensionality for action morphisms.
The underlying maps of `γ_R`, `γ_A` and `t` are identities.
Cohomology and scalar restriction preserve these identities. After removing
the identity compositions, both sides are definitionally the same underlying
canonical scalar comparison. This argument does not assert that `κφ`
itself is an identity and does not replace it by an arbitrary comparison.

## Simultaneous comparison on compatible diagrams

In namespace `EquivariantCoefficientDiagram`,
`restrictScalarsGroupCohomologyZeroFunctorIso` constructs

```text
restrictScalarsFunctor φ ⋙ restrictGroupFunctor ψ ⋙ cohomologyFunctor 0
  ≅
cohomologyFunctor 0 ⋙ scalar postcomposition ⋙ group postcomposition.
```

Here scalar postcomposition uses `(ModuleCat.restrictScalars φ).mapAction G`,
and group postcomposition uses `Action.res (ModuleCat R) ψ`.
Both are genuine functors on `J`-diagrams of module actions. The source
coefficient operations retain all equivariant geometric transition maps.
The construction uses the same sequence of whiskering and associators as
for a single equivariant sheaf.

Its `_hom_app` lemma identifies the component at `D` with
`restrictGroupCohomologyIso ψ (restrictScalars φ D) 0` followed by
postcomposition of the canonical scalar cohomology comparison with group
restriction. The lemma with suffix `_hom_app_app` identifies evaluation
at `i` with `scalarRestrictionGroupCohomologyZeroFunctorIso` at `D.obj i`.

The theorem `restrictScalarsGroup_cohomologyZero` identifies this route
with the opposite-order route: apply cohomology to the coefficient
interchange, use the scalar comparison on the group-restricted diagram,
then postcompose the group cohomology comparison with scalar restriction.
`NatTrans.ext` reduces the equality to
`scalarRestrictionGroup_cohomologyZero` at every vertex. The equation is
an equality of natural transformations, so it retains compatibility with
every diagram transition.

## Reindexing

The four lemmas whose names begin
`reindex_restrictScalarsCohomologyZeroFunctorIso` describe the existing
canonical scalar comparison after reindexing:

| Suffix | Equality |
| --- | --- |
| `_hom_app` | The forward component at `i` is the original component at `F.obj i`. |
| `_inv_app` | The inverse component at `i` is the original component at `F.obj i`. |
| `_hom` | The forward natural transformation is `Functor.whiskerLeft F` of the original one. |
| `_inv` | The inverse natural transformation is `Functor.whiskerLeft F` of the original one. |

All four are definitional equalities. Reindexing selects the original
coefficient object at `F.obj i`, and the canonical diagram comparison
is constructed from its vertex comparisons. The source and target
diagrams are identified by the published reindexing constructions.

## Scope

These are degree-zero comparisons for ordinary small-etale cohomology
and algebraic group actions. The module does not construct a positive-degree
cross-ring comparison, prove preservation of injectives, or implement
tensor extension, ideal reduction, inverse limits, smooth actions,
analytic sites, compact supports, or the Shimura specialization of Harris.
Those remain separate obligations.
