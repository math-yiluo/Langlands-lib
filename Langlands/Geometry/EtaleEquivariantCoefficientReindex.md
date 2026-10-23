# Reindexing equivariant coefficients over varying schemes

This internal construction extends the published equivariant coefficient
category by change of index. It imports
[EtaleEquivariantCoefficientDiagram](EtaleEquivariantCoefficientDiagram.md)
and [EtaleCohomologyReindex](EtaleCohomologyReindex.md). Its declarations lie in
`Langlands.Geometry.EtaleCohomologyAction.EquivariantCoefficientDiagram`.
It transcribes no external theorem: the coefficient laws are obtained from
the existing ordinary reindexing construction through the underlying sheaf
maps, and the comparisons follow from the actual component formulas.

## Inputs and variance

Let `R : Type u` be a commutative ring, let `J` be a category with objects in
universe `v` and morphisms in universe `w`, and let
`S : J ⥤ Scheme.{u}ᵒᵖ`. Every arrow `a : i ⟶ j` is assumed to induce an
etale scheme morphism

```text
f_a = (S.map a).unop : X_j ⟶ X_i,
X_i = (S.obj i).unop.
```

One fixed group `G : Type t` acts through supplied homomorphisms
`ρ i : G →* (Aut X_i)ᵐᵒᵖ`. The supplied condition `hρ` is

```text
f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a.
```

The opposite-automorphism convention and the meaning of equivariant sheaf
are exactly those of the imported coefficient category. In particular,
the coefficients are actual small-etale module sheaves with equivariant
transition maps satisfying sheaf-level identity and composition laws.

Let `K` have independent object and morphism universes `v'` and `w'`, and let
`F : K ⥤ J`. The reindexed geometry is `F ⋙ S`, with action
`i ↦ ρ (F.obj i)` and equivariance condition `a g ↦ hρ (F.map a) g`.
Etaleness of its maps is provided by the instance already imported from
`EtaleCohomologyReindex`. No change of the acting group occurs.

## Reindexing coefficients and morphisms

For an equivariant coefficient diagram `D`, `reindex F D` has

```text
(reindex F D).obj i = D.obj (F.obj i),
(reindex F D).map a = D.map (F.map a).
```

Its transition map has the required domain because equivariant restriction
for `F ⋙ S` at `a` is the restriction for `S` at `F.map a`.
For the identity and composition laws, the implementation applies
`TranslationAction.Equivariant.Hom.ext` to reduce the equations to equations
of underlying sheaf maps. The published underlying-map formulas for
`equivariantDiagramRestrictionId` and
`equivariantDiagramRestrictionComp` identify the relevant comparison
maps. Unfolding ordinary reindexing and forgetting then identifies the goals
with the laws of `CoefficientDiagram.reindex F D.forget`.
Thus the index functor's identity and composition equalities, including their
geometric equality transports, are handled by the existing ordinary
construction. No cohomological compatibility law is assumed.

For `α : D ⟶ E`, `reindexMap F α` has component `α.app (F.obj i)`.
Its transition square is `α.comm (F.map a)`. These operations define
`reindexFunctor F` from the original equivariant coefficient category to
the category for the reindexed geometry and actions. Identity and
composition preservation follow by coefficient-morphism extensionality
and definitional equality of their components.

## Forgetting and evaluation

`reindex_forget` proves

```text
(reindex F D).forget = CoefficientDiagram.reindex F D.forget.
```

`reindexForgetFunctorIso` packages this as an isomorphism natural in
coefficient diagrams:

```text
reindexFunctor F ⋙ forgetFunctor
  ≅ forgetFunctor ⋙ CoefficientDiagram.reindexFunctor F.
```

For each vertex `i : K`, `reindexEvaluationIso F i` is

```text
reindexFunctor F ⋙ evaluation i ≅ evaluation (F.obj i).
```

Both functor isomorphisms are `Iso.refl`: the functors have definitionally
equal object and morphism data, with proof irrelevance identifying the law
fields. Their components are identity maps of the relevant ordinary
coefficient diagrams or equivariant sheaves.

## Cohomology, sections and degree zero

For every natural degree `q`, `reindex_cohomology` proves an equality of
diagrams in `Action (ModuleCat.{u} R) G`:

```text
(reindex F D).cohomology q = F ⋙ D.cohomology q.
```

`reindex_sections` proves the analogous equality for `sections`.
These are reflexivity proofs: at a vertex they use the same supplied
equivariant coefficient sheaf, and at an arrow they use the same equivariant
geometric pullback followed by the same coefficient map. The cohomology is
the ordinary right-derived small-etale global-section functor from the
imported constructions.

The isomorphisms `reindexCohomologyFunctorIso F q` and
`reindexSectionsFunctorIso F` express these comparisons naturally in the
coefficient diagram. For example, writing `precompose F` for the functor
`(Functor.whiskeringLeft K J (Action (ModuleCat.{u} R) G)).obj F`, the first
has type

```text
reindexFunctor F ⋙ cohomologyFunctor q
  ≅ cohomologyFunctor q ⋙ precompose F.
```

The section comparison has the same form. Both are `Iso.refl`; in
particular their components preserve the actual group actions.

`reindex_cohomologyZeroIso_hom_app` and
`reindex_cohomologyZeroIso_inv_app` identify, in both directions, the
canonical degree-zero comparison at `i` for reindexed coefficients with
the original comparison at `F.obj i`. For example,

```text
(cohomologyZeroIso (reindex F D)).hom.app i
  = (cohomologyZeroIso D).hom.app (F.obj i).
```

These identities follow by reflexivity from the vertexwise construction
of the published canonical comparison.

## Identity and composition of reindexing

`reindexIdIso` identifies reindexing along `𝟭 J` with the identity functor
on equivariant coefficient diagrams.

For a further category `L` with independent universes `v''`, `w''` and a
functor `H : L ⥤ K`, `reindexCompIso F H` identifies

```text
reindexFunctor F ⋙ reindexFunctor H ≅ reindexFunctor (H ⋙ F).
```

The underlying scheme functors and action families at the target are
definitionally equal. On objects and morphisms both paths evaluate first
at `H` and then at `F`. These two comparisons are again implemented as
`Iso.refl`, using proof irrelevance for coefficient and functor law fields.
The file does not package a pseudofunctor or state separate higher
coherence laws.

## Scope

This is change of index for the supplied equivariant small-etale coefficient
data. It does not construct a specified tower or coefficient system, or
establish any property of a chosen index functor such as cofinality.
The acting group has no topology here; neither smoothness nor a change
of acting group is part of the construction. Analytic sites, compactly
supported cohomology, traces and a Harris specialization remain outside
this unit.
