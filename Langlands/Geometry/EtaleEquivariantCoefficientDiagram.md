# Equivariant coefficients over varying schemes

This module constructs a category of compatible equivariant small-étale
coefficient sheaves over a supplied diagram of schemes. Ordinary cohomology
in each natural degree and ordinary global sections give functors from this
category to diagrams of group actions on modules. Their canonical degree-zero
comparison is natural both along the scheme diagram and in its coefficients.

The declarations are in `Langlands.Geometry.EtaleCohomologyAction`; the
coefficient category's constructions are in its
`EquivariantCoefficientDiagram` namespace.

## Geometric and coefficient inputs

The coefficient ring is `R : Type u` with `[CommRing R]`. The index category
has objects `J : Type v` and morphisms in universe `w`. A functor
`S : J ⥤ Scheme.{u}ᵒᵖ` supplies the geometric diagram. Write
`X_i = (S.obj i).unop`; an arrow `a : i → j` induces the scheme morphism
`f_a = (S.map a).unop : X_j → X_i`. Every such map is required to be étale.

One group `G : Type t`, in an independent universe, acts on all the schemes.
The actions are supplied as
`ρ i : G →* (Aut X_i)ᵐᵒᵖ`, retaining the published opposite-automorphism
convention: `aut (ρ i) (g * h)` executes `aut (ρ i) g` and then
`aut (ρ i) h`. A supplied family `hρ` states that every scheme map is
equivariant:

```text
f_a ≫ aut(ρ_i,g).hom = aut(ρ_j,g).hom ≫ f_a.
```

No topology on `G` is required. The group is fixed across the entire diagram.
The construction is not an interface for varying groups or non-equivariant
scheme maps.

`equivariantDiagramRestriction a`, written `Q_a` below, is the published
canonical equivariant pullback along `f_a`. It maps actual small-étale
module sheaves with translation-equivariance on `X_i` to such sheaves on
`X_j`. Its underlying functor is the existing ordinary
`diagramRestriction R S a`.

`equivariantDiagramRestrictionId i` constructs `e_i : Q_id ≅ Id` using the
equivariant equality comparison for `S.map_id`, followed by the published
identity comparison. `equivariantDiagramRestrictionComp a b` constructs
`d_ab : Q_a ⋙ Q_b ≅ Q_(a≫b)` using the published composition comparison
and then equality transport along `S.map_comp`. These are constructed
comparisons, not additional supplied data. The two
`..._hom_app_hom` lemmas identify their underlying sheaf morphisms with
`diagramRestrictionId` and `diagramRestrictionComp`.

## Compatible equivariant coefficients

An `EquivariantCoefficientDiagram R S ρ hρ` consists of actual equivariant
sheaves `D.obj i` on `X_i` and equivariant sheaf morphisms

```text
D.map a : Q_a(D.obj i) → D.obj j.
```

The transition morphisms need not be isomorphisms. The supplied coefficient
compatibility laws are

```text
D.map(id_i) = e_i.hom(D.obj i),
d_ab.hom(D.obj i) ≫ D.map(a≫b)
  = Q_b(D.map a) ≫ D.map b.
```

These are laws on the coefficient sheaves. No cohomology groups, cohomology
transition maps, or cohomological identity/composition laws are record fields.
The module does not assert existence of coefficients realizing any particular
Harris tower.

`forget D` constructs the published ordinary `CoefficientDiagram R S` with
objects `(D.obj i).obj` and maps `(D.map a).hom`. Applying the underlying
morphism projection to the two coefficient laws proves its compatibility,
using the constructed comparison formulas.

`Hom D E` has an equivariant sheaf morphism `α.app i` at every vertex and the
commuting equation

```text
D.map a ≫ α.app j = Q_a(α.app i) ≫ E.map a.
```

`Hom.id` and `Hom.comp` construct pointwise identities and compositions;
functoriality of `Q_a` proves that they retain the commuting equation.
Extensionality of the pointwise maps proves the category laws. `id_app` and
`comp_app` expose these operations. `evaluation i` is the functor to the
equivariant coefficient category on `X_i`.

`forgetFunctor` sends this category to `CoefficientDiagram R S`.
Its faithfulness is proved by pointwise extensionality and faithfulness of
forgetting equivariant morphisms to their underlying sheaf morphisms.
Fullness or equivalence is not asserted.

## Ordinary cohomology with actions

For `q : ℕ`, `D.cohomology q` is a functor

```text
J → Action (ModuleCat.{u} R) G.
```

At vertex `i` it is the published
`pullbackCohomologyFunctor R (ρ i) q` evaluated at `D.obj i`. Its underlying
module is ordinary degree-`q` small-étale module cohomology, defined by
right-derived global sections. Along `a : i → j`, the map is the composite
of geometric equivariant cohomology pullback and the cohomology map of the
coefficient transition:

```text
H^q(X_i,D_i) → H^q(X_j,Q_a D_i) → H^q(X_j,D_j).
```

Both factors are already morphisms of `G`-actions. To prove the functor's
identity and composition laws, the implementation applies `Action.Hom.ext`,
identifies the two underlying factors with ordinary geometric pullback and
ordinary coefficient cohomology, and uses the laws of
`D.forget.cohomology q`. Thus the new action-valued functor derives its laws
from the actual coefficient data and the published ordinary construction.
`cohomology_map_hom` proves that its underlying transition is exactly
`(D.forget.cohomology q).map a`.

For `α : D → E`, `cohomologyMap α q` has component
`(pullbackCohomologyFunctor R (ρ i) q).map (α.app i)`.
Naturality follows by forgetting the actions and applying the ordinary
coefficient-diagram naturality theorem. `cohomologyFunctor q` packages this
assignment into a functor in the equivariant coefficient diagram.
Its identity and composition laws are the pointwise laws of the published
equivariant coefficient cohomology functors.

## Ordinary sections and the degree-zero comparison

`D.sections` also lands in `Action (ModuleCat R) G`. At each vertex it uses
`pullbackSectionsFunctor`. Its arrow map is equivariant geometric section
restriction followed by the section map of `D.map a`. This is the direct
section map, with the published geometric group action.

The functor laws are proved using `Action.Hom.ext` and the ordinary
`D.forget.sections` laws. The ordinary `CoefficientDiagram.sections_map`
formula identifies the published degree-zero-transport presentation of
those maps with direct restriction followed by the coefficient map.
`sections_map_hom` records equality with the ordinary diagram's transition.

`sectionsMap α` has component
`(pullbackSectionsFunctor R (ρ i)).map (α.app i)`. Its naturality follows
from the ordinary section-diagram naturality equation after applying
`CoefficientDiagram.sectionsFunctor_map_app`. `sectionsFunctor` packages
these maps with pointwise identity and composition proofs.

`cohomologyZeroIso D : D.cohomology 0 ≅ D.sections` has at vertex `i` the
published canonical equivariant comparison
`(pullbackCohomologyZeroFunctorIso R (ρ i)).app (D.obj i)`. Its naturality
along `a` follows from the comparison's naturality in the coefficient
transition and `equivariantPullbackCohomology_zero` for the scheme map.
Finally, `cohomologyZeroFunctorIso` makes this comparison natural in `D`;
its coefficient naturality proof is the pointwise naturality of the same
published comparison.

## Provenance and scope

This is an internal categorical extension of the published
[equivariant pullback](EtaleEquivariantPullback.md),
[pullback functoriality](EtaleEquivariantPullbackFunctoriality.md),
[equality and coherence comparisons](EtaleEquivariantPullbackCoherence.md),
[ordinary coefficient diagrams](EtaleCohomologyDiagram.md),
[ordinary coefficient functors](EtaleCohomologyDiagramFunctor.md), and
[equivariant cohomology functors](EtaleActionFunctor.md). The category uses
pointwise morphisms and their explicit commuting laws. The cohomology and
section laws are derived through the existing ordinary functors, while
equivariance is retained by composing their published action-valued lifts.
The construction does not transcribe or claim a named theorem from Harris
or Berkovich.

The schemes, their compatible actions, and the étale geometric diagram
remain inputs, as do the sheaves and their coefficient compatibility laws.
No packaged pseudofunctor, change-of-index construction, nontrivial
coefficient existence result, analytic site, topology or smoothness of
the group action, compact supports, trace map, actual Shimura tower, or
Harris specialization is constructed in this module.
