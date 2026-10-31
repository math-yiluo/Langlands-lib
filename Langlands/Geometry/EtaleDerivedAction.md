# Geometric group actions on bounded-below derived etale sections

Let `Y : Scheme.{u}`, let `R : Type u` be a commutative ring, and let
`G : Type w` be a group. An actual homomorphism
`ρ : G →* (Aut Y)ᵐᵒᵖ` supplies the scheme action, with the opposite convention
already used in `EtaleCohomologyAction`. Choose derived localizations of the
small-etale module-sheaf category and of `ModuleCat.{u} R` in independent
universes `wS` and `wT`. The group universe is independent of both.

`pullbackDerivedSectionsFunctor` maps actual equivariant coefficient sheaves
to group actions on their actual bounded-below derived-section objects.
It first applies the published `ofEquivariantFunctor` to obtain compatible
coefficients on `actionSchemeDiagram ρ`, then applies the new
`CoefficientDiagram.derivedSectionsFunctor`, and finally uses Mathlib's
equivalence between `SingleObj G` diagrams and actions in a category.
The functor and action laws therefore follow from the proved diagram laws
and this equivalence. They are not input equations about derived sections.

The underlying object at a sheaf `F` is `RΓ(Y,F.obj)`. The map underlying an
equivariant coefficient morphism `f` is precisely the actual derived-section
map of `f.hom`, as `pullbackDerivedSectionsFunctor_map_hom` states.
For `g : G`, `pullbackDerivedSectionsFunctor_obj_ρ` identifies its derived
action with geometric pullback along `(aut ρ g).hom`, followed by derived
sections of the coefficient structure morphism `F.act g`. Both formulas
follow directly from the construction.

For `q : ℕ`, `pullbackDerivedHomologyIso F q` identifies the action obtained
by applying cohomology to this derived action with the previously constructed
`pullbackCohomologyAction R ρ F q`. Its underlying isomorphism is the canonical
`EtaleDerivedSectionsPlus.homologyNatIso` component. Equivariance is exactly
the recovery theorem for derived pullback with a target coefficient map,
together with the published formula for the ordinary geometric action.
`pullbackDerivedHomologyFunctorIso q` makes the comparison natural in
equivariant coefficients, by applying coefficient naturality of that same
canonical comparison. `pullbackDerivedHomologyIso_hom_hom` records the
underlying map explicitly.

Composing the degree-zero comparison with the published ordinary
cohomology-to-sections comparison gives `pullbackDerivedZeroFunctorIso`.
Its underlying component is the canonical derived-cohomology-to-sections
isomorphism, as the final theorem proves by expanding that composite.
Thus the constructed action recovers the ordinary action on sections,
equivariantly and naturally in the coefficients.

The provenance is internal: this lifts the published actual scheme-action
coefficient diagram through the derived geometric construction and reuses
its proved ordinary-cohomology comparison. This is an action in D⁺ itself;
it does not assert a strict action on a chosen raw injective-resolution
complex. The group has no topology here, so no continuity or smoothness is
claimed. A specific arithmetic Galois or Harris action still requires its
actual scheme action and equivariant coefficient sheaves. Compact support,
scalar change, inverse limits and Harris-space realization remain outside
this construction.
