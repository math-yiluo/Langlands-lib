# Group restriction of equivariant coefficient diagrams

This module constructs restriction of the acting group for compatible
equivariant small-etale coefficient diagrams. It retains the entire ordinary
coefficient diagram and identifies the resulting cohomology and section
diagrams with restriction of their original group actions. These comparisons
are natural in both the scheme-diagram arrows and the coefficients.

All declarations lie in
`Langlands.Geometry.EtaleCohomologyAction.EquivariantCoefficientDiagram`.

## Inputs and conventions

Let `R : Type u` be a commutative ring. Let `J` have objects in universe `v`
and morphisms in universe `w`, and let `S : J ⥤ Scheme.{u}ᵒᵖ`. Write
`X_i = (S.obj i).unop`. Every arrow `a : i ⟶ j` is assumed to induce an
etale scheme morphism `f_a = (S.map a).unop : X_j ⟶ X_i`.

The group `G : Type t` acts through supplied homomorphisms
`ρ i : G →* (Aut X_i)ᵐᵒᵖ`. The opposite-automorphism convention is inherited
from the published construction: `aut (ρ i) (g * h)` executes
`aut (ρ i) g` and then `aut (ρ i) h`. The supplied condition `hρ` states

```text
f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a.
```

Let `H : Type t'` be another group, in an independent universe, and let
`φ : H →* G`. No injectivity or topology is required. The restricted action
on `X_i` is `(ρ i).comp φ`; its geometric equivariance equation at `h : H`
is the original equation `hρ a (φ h)`.

The input `D : EquivariantCoefficientDiagram R S ρ hρ` consists of actual
equivariant module sheaves on the small-etale sites, with equivariant
coefficient transition maps satisfying the published sheaf-level identity
and composition laws. Its construction and conventions are described in
[EtaleEquivariantCoefficientDiagram](EtaleEquivariantCoefficientDiagram.md).

## Restriction of coefficients and morphisms

`restrictGroup φ D` has coefficient sheaf
`(restrictionFunctor R (ρ i) φ).obj (D.obj i)` at `i`. Its transition at
`a : i ⟶ j` is

```text
(restrictionFunctor R (ρ j) φ).map (D.map a).
```

This has the required source because group restriction and equivariant
geometric pullback have definitionally equal composites, as exposed by
the published `restrictionPullbackIso` in
[EtalePullbackGroupRestriction](EtalePullbackGroupRestriction.md).
The underlying coefficient sheaf and transition map are unchanged.
The identity and composition laws follow by equivariant-morphism
extensionality, the published underlying formulas for the geometric
comparison maps, and the laws of `D.forget`. In particular, no cohomology
compatibility is an input.

`restrictGroup_forget` identifies `(restrictGroup φ D).forget` with
`D.forget` by reflexivity. `restrictGroupMap φ α` restricts each component
`α.app i`; its transition equation follows by projecting the original
equivariant equation to its underlying sheaf equation.
`restrictGroupFunctor φ` packages these constructions. It preserves
identities and composition by the pointwise laws of `restrictionFunctor`.
Its faithfulness follows from faithfulness of group restriction at each
vertex.

Two natural comparisons are given by `Iso.refl`:

```text
restrictGroupForgetFunctorIso:
  restrictGroupFunctor φ ⋙ forgetFunctor ≅ forgetFunctor,

restrictGroupEvaluationIso i:
  restrictGroupFunctor φ ⋙ evaluation i
    ≅ evaluation i ⋙ restrictionFunctor R (ρ i) φ.
```

Their object and morphism data are definitionally equal; proof irrelevance
identifies their law fields. Their components are identity morphisms of
ordinary coefficient diagrams or restricted equivariant sheaves, respectively.

## Cohomology and sections

For `q : ℕ`, `restrictGroupCohomologyIso φ D q` is a natural isomorphism
of `H`-action-valued diagrams:

```text
(restrictGroup φ D).cohomology q
  ≅ D.cohomology q ⋙ Action.res (ModuleCat.{u} R) φ.
```

At `i` it is the published comparison
`(restrictionCohomologyFunctorIso R (ρ i) φ q).app (D.obj i)`.
This comparison has identity underlying module map and identifies the
restricted action at `h` with the original action at `φ h`.
The underlying module is ordinary degree-`q` small-etale cohomology, defined
by right-derived global sections.

Naturality along `a : i ⟶ j` is proved by `Action.Hom.ext`.
The published `cohomology_map_hom` formula and `restrictGroup_forget`
identify both underlying transitions with
`(D.forget.cohomology q).map a`. The comparison components are identities,
so the square follows from the category identity laws.

`restrictGroupCohomologyFunctorIso φ q` makes this comparison natural in
`D`. Its right-hand functor applies `cohomologyFunctor q` and then
postcomposes its output with `Action.res (ModuleCat R) φ`, using
`Functor.whiskeringRight`. The proof is pointwise naturality of the
published `restrictionCohomologyFunctorIso`.

`restrictGroupSectionsIso φ D` and `restrictGroupSectionsFunctorIso φ`
give the analogous comparisons for ordinary global sections:

```text
(restrictGroup φ D).sections
  ≅ D.sections ⋙ Action.res (ModuleCat.{u} R) φ.
```

Their vertex components are `restrictionSectionsFunctorIso`; naturality
along the scheme diagram reduces to `D.forget.sections.map a` and the
category identity laws. Naturality in the coefficients is the pointwise
section comparison's naturality.

`restrictGroup_cohomologyZero` proves an equality of natural
transformations. First identifying the restricted degree-zero cohomology
and then restricting the original canonical degree-zero comparison equals
first applying the canonical degree-zero comparison for restricted
coefficients and then identifying the section diagrams. Evaluation at
each vertex reduces the equation to the published
`restriction_cohomologyZero` theorem.

## Identity, composition, and change of index

`restrictGroupIdIso` identifies restriction along `MonoidHom.id G` with
the identity functor on the coefficient category.

For a group `K : Type t''` and `ψ : K →* H`, `restrictGroupCompIso φ ψ`
identifies successive restriction along `φ` and `ψ` with restriction along
`φ.comp ψ`.

For a category `I` with independent object and morphism universes `v'`
and `w'`, and `F : I ⥤ J`, `reindexRestrictGroupIso φ F` identifies

```text
reindexFunctor F ⋙ restrictGroupFunctor φ
  ≅ restrictGroupFunctor φ ⋙ reindexFunctor F.
```

All three comparisons are implemented by `Iso.refl`: their underlying
sheaves, action maps, transition maps, and coefficient-morphism components
are definitionally equal, with proof irrelevance for the law fields.
The last comparison uses the published
[reindexing functor](EtaleEquivariantCoefficientReindex.md).
No separate higher coherence assertions are made.

## Provenance and scope

This is an internal categorical construction from the imported Library
interfaces. [EtaleActionRestriction](EtaleActionRestriction.md) supplies
pointwise group restriction and its cohomology, section, and degree-zero
comparisons. The two directly imported modules supply coefficient
reindexing and the interchange with geometric pullback. The new
coefficient laws and naturality equations are derived from these actual
formulas. No named Harris or Berkovich theorem is transcribed or assumed.

The schemes, their compatible actions, the etale diagram, the coefficient
sheaves, and `φ` remain supplied data. One fixed group acts across each
diagram; this module changes that group uniformly and does not allow
different groups at different vertices. It constructs neither an actual
Harris tower nor a specified coefficient system. It asserts no analytic
site, topology, smoothness, compact support, trace, or cohomology comparison
beyond the ordinary constructions explicitly described above.
