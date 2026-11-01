# Canonical deck actions on restricted étale coefficients

Author: Worker 13. This is an internal construction from the actual restriction,
equivariant-pullback and derived-section constructions in
`EtalePullback`, `EtaleEquivariantPullback`, `EtaleDerivedAction` and
`EtaleDerivedEquivariantMap`. It introduces no new external theorem or
literature convention.

## Geometry and scope

Let `X` and `Z` be schemes in universe `u`, let `R : Type u` be a commutative
ring, and let `G : Type t` be a group. A homomorphism
`τ : G →* (Aut Z)ᵐᵒᵖ` gives the existing left-action convention:
`aut τ (g * h) = aut τ g ≪≫ aut τ h`. Let `f : Z ⟶ X` be étale and suppose
`aut τ g |>.hom ≫ f = f` for every `g`. This is the sole additional
compatibility hypothesis: a geometric deck condition on scheme morphisms.
It neither supplies equivariance of coefficients nor assumes any action on
cohomology. The construction does not require the cover to be finite,
surjective or Galois, or the action to be faithful.

Coefficients are actual small-étale module sheaves with fixed scalars `R`.
Derived sections put the sheaf in degree zero and apply the existing actual
right-derived global-section functor into
`DerivedCategory.Plus (ModuleCat R)`. The choices of derived localizations
for the source sheaf category, target sheaf category and module category
have independent universes `wX`, `wZ`, `wT`. The group universe is independent.
Sections are ordinary global sections, with no compact-support convention.

## Constructed equivariance

`trivialEquivariantSheaf` gives every sheaf on `X` its canonical equivariance
for the trivial scheme action `1 : G →* (Aut X)ᵐᵒᵖ`. Each structure map is
precisely the existing `restrictionId` comparison. The unit and multiplication
laws reduce to equality of the actual small-étale site morphisms after applying
the coefficient presheaf. `trivialEquivariantFunctor` acts on coefficient
morphisms by the original morphism; naturality of `restrictionId` proves its
equivariance. `trivialEquivariantForgetIso` is the identity comparison with
the original coefficient functor.

`deckEquivariantMap` converts the deck condition into equivariance of `f`
for the trivial action on `X` and the action `τ` on `Z`.
`deckEquivariantFunctor` first applies the constructed trivial equivariance
and then the existing actual `equivariantPullback`. Thus its underlying
sheaf is exactly restriction along `f`, and its structure map at `g` is

```
(equivariantRestrictionIso R 1 τ f … g).inv.app F ≫
  (restriction f (ModuleCat R)).map ((restrictionId (ModuleCat R)).hom.app F).
```

`deckEquivariantFunctor_obj_act` records that formula.
The comparison square comes from composition and equality of the actual
scheme maps. Its inverse, followed by the restricted identity comparison,
constructs the coefficient action. The already proved equivariant-pullback
unit and multiplication laws give its intrinsic laws.
`deckEquivariantForgetIso` is the identity isomorphism with ordinary
restriction, and `deckEquivariantFunctor_map_hom` identifies every coefficient
arrow with its actual restricted arrow.

## Derived and ordinary actions and maps

`deckSectionsFunctor`, `deckCohomologyFunctor q` and
`deckDerivedSectionsFunctor` apply the corresponding existing geometric-action
functors to these canonically equivariant restricted coefficients. They are
functors of all original coefficient morphisms, so postcomposing any coefficient
diagram retains every transition equivariantly. In particular, coefficient
transitions need not be isomorphisms.

`deckDerivedSectionsFunctor_obj_ρ` identifies the derived action of `g` with
actual derived geometric pullback along `aut τ g |>.hom`, followed by derived
sections of the constructed structure map above. Its underlying coefficient
maps are the actual derived-section maps of the restricted morphisms, as stated
by `deckDerivedSectionsFunctor_map_hom`.

`deckSectionsMap`, `deckCohomologyMap q` and `deckDerivedSectionsMap` whisker
the existing equivariant geometric maps by `trivialEquivariantFunctor`.
They are therefore natural in every original coefficient sheaf and are maps
of actions. Their `app_hom` lemmas identify the underlying maps with exactly
the original geometric section, cohomology and derived-section restrictions.
Their sources use the constructed trivial equivariance, with no independently
chosen source action. `trivialEquivariantDerivedAction` proves the resulting
source derived action is the identity for every group element by the actual
derived geometric identity law `derivedSectionsMap_id`.
`deckDerivedSectionsMap_invariant` consequently proves that each deck element
fixes the actual derived restriction map, using its equivariance equation.
It does not deduce an equality of derived maps from homology.

## Canonical recovery and remaining obligations

`deckDerivedHomologyIso q` and `deckDerivedZeroIso` whisker the existing
canonical equivariant comparisons by `deckEquivariantFunctor`, with the
functor associator. They recover respectively ordinary degree-`q` cohomology
and ordinary sections, including the actions and naturality in all original
coefficients. `q : ℕ` is a cohomological degree.
`deckDerivedSectionsMap_homology` and `deckDerivedSectionsMap_zero` prove
that derived geometric restriction commutes with those specified comparisons
and the corresponding ordinary maps. After removing the identity associator
components their proofs are exactly the existing equivariant recovery squares.

This is a canonical abstract group action for étale restriction, with fixed
scalars and ordinary derived sections of sheaves initially in degree zero.
No topology on `G`, smoothness or continuity is asserted. Arbitrary non-étale
base change, including unrestricted algebraic-closure base change, is outside
this restriction construction. The specific Harris schemes and independently
separating towers, comparison with independently associated base-changed torsor
systems, compact supports, traces, scalar change, inverse limits, adelic and
continuous arithmetic actions, analytic uniformization and Ext applications
remain separate constructions. This unit does not complete the broad Harris task.
