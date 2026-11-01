# Canonical deck actions on the full restricted Harris coefficient system

Author: Worker 13.

This is an internal specialization of the
[canonical geometric deck construction](../../Geometry/EtaleDeckAction.md)
to the full [Harris coefficient system](HarrisEtaleCoefficients.md) and its
[actual geometric derived pullback](HarrisEtaleDerivedPullback.md).
It asserts no new original-literature theorem. The imported Harris modules
retain the original lattice and coefficient provenance.

## Parameters and geometric hypotheses

Retain the original finite rational algebra `A : Type u` with involution
`σ`, number field `L : Type u`, finite-dimensional `L`-module `W : Type u`,
algebraic representation `ρ` of `σ.baseChange L`, rational finite place `p`,
compact open finite-adelic level `U`, and arbitrary parameter `m : ℕ`.
The supplied scheme is `X : Scheme.{u}`. The diagram `Y` consists of actual
small-etale objects over `X` with the original `harrisCongruenceGroups`
actions, and every `Y.action n` satisfies `IsFiniteGeometricTorsor X`.
These are genuine geometric torsor hypotheses.

Write `R = HarrisCoefficientIntegers L p` and
`C = harrisEtaleCoefficientSystem ρ p U m X Y hY`. The coefficient ring
contains every coefficient place of `L` above `p`, and `C` retains the full
stable lattice, every exponent of `ℕᵒᵖ` including zero, and every original
transition. No nonzero hypothesis on `m` is introduced; `m` is not identified
with a residue characteristic.

Let `G : Type t` be a group, let `Z : Scheme.{u}`, and let
`τ : G →* (Aut Z)ᵐᵒᵖ`. The existing convention is
`aut τ (g * h) = aut τ g ≪≫ aut τ h`.
For an etale morphism `f : Z ⟶ X`, assume

```text
hf : ∀ g, (aut τ g).hom ≫ f = f.
```

This geometric deck equation supplies the compatibility with the trivial
action on `X`. No coefficient equivariance or cohomology action is an input.
There is no finiteness, surjectivity, Galois or faithfulness hypothesis on
this additional morphism and action. The finite geometric torsor assumptions
on the separate input diagram `Y` remain in force.

## Constructed coefficient actions and transitions

`harrisEtaleDeckCoefficientSystem` is

```text
C ⋙ deckEquivariantFunctor R τ f hf.
```

The generic functor first constructs trivial equivariance on each original
sheaf using the identity-restriction comparison, then applies actual
equivariant pullback along `f`. In particular, its structure morphism at
`g` is the inverse comparison for the commuting geometric square, followed
by restriction of that identity-restriction comparison. Its unit and
multiplication laws are the already proved intrinsic laws of this construction.

`harrisEtaleDeckCoefficientForgetIso` identifies the underlying functor with
the existing `harrisEtaleRestrictedCoefficientSystem`; this is definitionally
the identity comparison. The `_map_hom` equation identifies every underlying
arrow with the previously constructed restricted arrow. The `_map_factors`
equation writes it as restriction of the original lattice reduction followed
by restriction of the inverse geometric torsor comparison. It uses the
existing restricted transition formula. Thus the deck construction preserves
all original transition data, including transitions which are not isomorphisms.

## Ordinary and derived systems and geometric maps

`harrisEtaleDeckSectionsSystem` and `harrisEtaleDeckCohomologySystem q`
postcompose `C` with the generic deck section and cohomology functors.
Their source counterparts `harrisEtaleTrivialSectionsSystem` and
`harrisEtaleTrivialCohomologySystem q` use the constructed trivial coefficient
equivariance on `X`. Here `q : ℕ` is a cohomological degree, independent of
the coefficient exponent.

`harrisEtaleDeckSectionsPullback` and
`harrisEtaleDeckCohomologyPullback q` left-whisker the generic geometric maps
by `C`. They are natural transformations of whole inverse systems in
`Action (ModuleCat R) G`. Their `_app_hom` equations identify the underlying
components with the existing Harris geometric restriction maps. Forgetting
the target actions recovers the previous restricted systems: the cohomology
comparison is definitionally the identity, while the section comparison uses
identity components and the generic section functor's underlying-map equation
to prove naturality.

`harrisEtaleTrivialDerivedPlusSystem` and
`harrisEtaleDeckDerivedPlusSystem` construct the corresponding whole systems
in `Action (DerivedCategory.Plus (ModuleCat R)) G`. These use ordinary global
sections, with sheaves placed in degree zero before applying the actual
bounded-below right-derived section functor. The source sheaf, target sheaf
and module derived localizations have independent universes `wX`, `wZ`, `wT`;
the abstract group has the independent universe `t`. Schemes and scalar
carriers share `u`. The systems are diagrams of derived objects.

`harrisEtaleTrivialDerivedPlusSystem_ρ` proves that each source derived
action is the identity, using the actual geometric derived identity law.
`harrisEtaleDeckDerivedPlusSystem_ρ` identifies the target action with
actual derived geometric pullback along the deck automorphism, followed by
derived sections of the constructed coefficient structure morphism.
The `_map_hom` equation retains precisely the existing restricted derived
coefficient transitions.

`harrisEtaleDeckDerivedPlusPullback` left-whiskers the generic equivariant
derived map by `C`. Its `_app_hom` equation identifies its underlying
component with the previously constructed `harrisEtaleDerivedPlusPullback`.
The two derived forgetful isomorphisms recover the original source system
and the existing restricted target system by identity comparisons.
The `_invariant` theorem proves that every deck element fixes each actual
Harris derived pullback map. Its proof specializes the generic invariance
equation and rewrites the underlying map to its existing Harris name.
Source triviality and invariance are equalities in the derived category;
they are not inferred from equalities on homology.

## Canonical equivariant recovery

`harrisEtaleDeckDerivedPlusCohomologyIso q` and
`harrisEtaleDeckDerivedPlusZeroIso` recover the target ordinary cohomology
and section systems as systems with actions. Their source counterparts
`harrisEtaleTrivialDerivedPlusCohomologyIso q` and
`harrisEtaleTrivialDerivedPlusZeroIso` use the canonical comparisons for the
constructed trivial coefficient equivariance. All four natural isomorphisms
use the specified generic component comparisons; their naturality follows
from the generic comparisons applied to each original coefficient transition.

The four `_hom_app_hom` theorems show that forgetting actions on these
comparison maps gives exactly the previously named Harris source and
restricted-target canonical comparisons. The target proofs expand the
identity associator components and use the generic canonical comparisons.
The source degree-zero proof additionally uses the existing equality between
the Harris and generic whole-system zero comparisons. Thus the construction
preserves the previous comparison maps.

`harrisEtaleDeckDerivedPlusPullback_homology q` proves the square

```text
homology of equivariant derived pullback ≫ target canonical comparison
  = source canonical comparison ≫ equivariant cohomology pullback.
```

The `_zero` theorem proves its degree-zero counterpart with ordinary section
pullback. These are equalities of natural transformations of entire action
systems. Their proofs apply natural-transformation extensionality and the
generic equivariant recovery square at each original sheaf `C.obj n`.
Every coefficient transition is retained by the functors and comparisons.

## Remaining obligations

This construction uses one fixed integral coefficient ring and ordinary
small-etale global sections for supplied schemes and torsors. The additional
deck group is abstract; no topology, smoothness or continuity is asserted.
Identifying the supplied geometry with the particular Harris Shimura schemes
and independently separating tower remains separate. The target is actual
restriction along the etale map `f`; comparison with sheaves independently
associated to base-changed torsors is not constructed here. Arbitrary
non-etale base change, including unrestricted algebraic-closure pullback,
compact supports, traces, scalar change, inverse limits, adelic and continuous
arithmetic actions, analytic uniformization and Ext applications remain
separate obligations. This specialization does not complete the broad
Harris framework task.
