# Actual geometric pullback of the full Harris derived coefficient system

Author: Worker 13.

This internal construction specializes
[whole-system actual derived pullback](../../Geometry/EtaleDerivedSystemPullback.md)
to the published full [Harris sheaf system](HarrisEtaleCoefficients.md) and
[its actual derived system](HarrisEtaleDerivedPlus.md). It asserts no new
original-literature theorem. The original lattice and coefficient provenance
remains in the imported Harris modules.

## Parameters and target coefficients

Retain all parameters and hypotheses of `harrisEtaleCoefficientSystem`:
a finite rational algebra `A : Type u` with involution `σ`, a number field
`L : Type u`, a finite-dimensional `L`-module `W : Type u`, an algebraic
representation `ρ` of `σ.baseChange L`, a rational finite place `p`, a
compact open finite-adelic level `U`, and an arbitrary scalar parameter
`m : ℕ`. The input scheme is `X : Scheme.{u}`. The diagram `Y` consists
of actual small-etale objects over `X`, equivariant for the original
`harrisCongruenceGroups ρ p U m`, and each `Y.action n` satisfies the genuine
geometric predicate `IsFiniteGeometricTorsor X`. These are geometric
torsor assumptions, not assumed cohomology or derived comparisons.

Write `R = HarrisCoefficientIntegers L p` and
`C = harrisEtaleCoefficientSystem ρ p U m X Y hY`. The coefficient ring
retains every place of `L` above `p`; the coefficient diagram retains the
whole stable lattice and every exponent in `ℕᵒᵖ`, including zero.
No nonzero hypothesis on `m` is used or inferred. The parameter `m` is
not implicitly identified with a residue characteristic.

For an actual etale scheme map `f : Z ⟶ X`,
`harrisEtaleRestrictedCoefficientSystem` is exactly

```text
C ⋙ EtalePullback.restriction f (ModuleCat R).
```

The target contains the restricted sheaves and every restricted coefficient
transition. The `_map` equation expresses each such transition as restriction
of the original coefficient reduction, followed by restriction of the inverse
of the proved geometric torsor comparison. It follows from the original
Harris transition formula and the restriction functor's composition law.
The construction does not supply or assume an identification with sheaves
independently associated to base-changed torsors.

## Actual systems and maps

`harrisEtaleRestrictedSectionsSystem`,
`harrisEtaleRestrictedCohomologySystem q` and
`harrisEtaleRestrictedDerivedPlusSystem` postcompose this actual restricted
sheaf system with ordinary sections, degree-`q` ordinary cohomology, and
bounded-below derived sections on `Z`, respectively. Here `q : ℕ` is a
cohomological degree distinct from the coefficient exponent. The derived
functor places sheaves in degree zero and applies actual right-derived global
sections. The source and target sheaf derived localizations use independent
universes `wX`, `wZ`, and the module localization uses `wT`; the intermediate
scheme in composition has its own `wV`. All schemes and scalars share `u`.

`harrisEtaleSectionsPullback`, `harrisEtaleCohomologyPullback q` and
`harrisEtaleDerivedPlusPullback` specialize the corresponding generic
whole-system maps. Their source systems are the existing Harris systems.
They are natural transformations of whole inverse diagrams, so they retain
all coefficient transitions. The derived `_app` equation identifies each
component with actual derived geometric pullback of `C.obj n`; the
`_naturality` equation records its square for every original coefficient
transition. The maps are constructed using the actual geometric derived
map, not inferred from their effects on cohomology.

## Canonical recovery and geometric laws

`harrisEtaleRestrictedDerivedPlusCohomologyIso q` and
`harrisEtaleRestrictedDerivedPlusZeroIso` use the generic canonical recovery
isomorphisms for the restricted system. The source comparison equalities
`harrisEtaleDerivedPlusCohomologyIso_eq_system` and
`harrisEtaleDerivedPlusZeroIso_eq_system` identify the existing Harris
comparisons with the generic ones. The first is definitional; the second expands the comparison
definitions, distributes left whiskering over composition and applies
associativity of isomorphism composition. This preserves the previously specified source comparisons.

`harrisEtaleDerivedPlusPullback_homology` proves the commuting square
between homology of the actual derived pullback and ordinary cohomology
pullback under these canonical comparisons. The `_zero` equation gives
the corresponding ordinary-section square. Both specialize the generic
whole-system equations, with the source degree-zero comparison rewritten
by its proved equality.

`harrisEtaleDerivedPlusPullback_id` proves that pullback along the identity,
followed by derived sections of the canonical identity-restriction
comparison, is the identity of the full Harris derived system. For etale
`g : V ⟶ Z`, `_comp` proves that pullback along `f`, then pullback of the
restricted system along `g`, followed by derived sections of the canonical
`restrictionComp` comparison, is pullback along `g ≫ f`. Its second map
uses the same restricted coefficient system; it introduces no independently
associated torsor system on `Z`. Both equalities are proved in the actual
derived category by the generic geometric laws, not by detecting equality
through homology.

## Remaining obligations

These are ordinary global sections and cohomology over one fixed integral
coefficient ring, along etale scheme maps, for supplied actual geometric
torsors. Identifying the supplied schemes and torsors with the particular
Harris Shimura tower and its independently separating levels remains a
separate geometric obligation. This module does not construct associated
sheaf base-change comparisons, compact supports, traces, scalar extension,
derived inverse limits, smooth adelic actions, continuous arithmetic Galois
actions, uniformization, or the representation-theoretic Ext spectral
sequence. It makes no assertion that cohomology commutes with a limit.
