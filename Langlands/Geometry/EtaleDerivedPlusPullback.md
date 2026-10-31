# Geometric pullback of bounded below derived etale sections

Author: Worker 13.

For actual schemes `X`, `Y` in universe `u`, an etale morphism
`f : Y ⟶ X` and a commutative ring `R : Type u`, this module constructs
geometric pullback of derived sections of module sheaves:

\[
R\Gamma(X,F)\longrightarrow R\Gamma(Y,f^*F).
\]

The coefficient sheaves are `EtaleDerivedSections.ModuleSheaf`, namely
sheaves of `ModuleCat.{u} R` on Mathlib's small etale sites. Here `f^*`
means the existing `EtalePullback.restriction f (ModuleCat R)`: evaluate
on an etale `Y`-scheme by composing its structure map with `f`.
The source and target are the actual
`EtaleDerivedSectionsPlus.derivedSections` objects in
`DerivedCategory.Plus (ModuleCat R)`. They apply the right derived
global-section functor to a sheaf placed in degree zero.

The two sheaf derived categories and the module derived category have
independent localization universes `wX`, `wY`, `wT`; the scheme and scalar
carriers share universe `u`. Enough injectives for the actual sheaf
categories is inferred from Mathlib, rather than supplied as new data.
Cochain degrees are integers; `q : ℕ` indexes nonnegative cohomology.

## The derived map

`derivedSectionsMap f R` is a natural transformation from
`derivedSections X R` to `restriction f (ModuleCat R) ⋙ derivedSections Y R`.
It specializes `DerivedPlusSource.derivedMap` to the genuine natural
section restriction `sectionsMap f R`. The published exactness and
injective-preservation instances for etale restriction provide all source
functor hypotheses. No derived map or compatibility theorem is assumed.

For any injective resolution `I` of `F`,
`derivedResolutionSectionsMap f R I` applies `sectionsMap` in each
natural degree and extends the resulting chain map by zero to integer
degrees. Its target is sections of `restrictedResolution f R I`,
extended in the same way. `derivedSectionsMap_app` proves that the
derived map is the localization of this chain map, conjugated by the
canonical image-resolution identifications. Resolution independence
and coefficient naturality are inherited from the generic construction.

## Ordinary cohomology and degree zero

`derivedSectionsMap_homology` proves that for every `q : ℕ` the map on
cohomology, under the published `homologyNatIso` identifications, is
exactly `EtalePullback.cohomologyMap f R q`. In particular, this is a
comparison of the actual constructed morphisms, not only of their
source and target objects.

The proof computes both sides with `injectiveResolution F`.
On the target it uses the restricted resolution to compute the
resolution-independent natural cohomology isomorphism. The generic
`derivedMap_homology` formula then agrees with the existing
`cohomologyMap_app` formula term by term.

`derivedSectionsMap_zero` further identifies degree-zero cohomology of
the derived map with the original `sectionsMap f R`, using the
canonical `homologyZeroIso` identifications of degree-zero derived
cohomology with global sections. Its proof combines the preceding
cohomology comparison with the published `cohomologyMap_zero`.

For `α : f^*F ⟶ G`, `derivedSectionsMapWithCoefficients f R α` composes
geometric pullback with the derived-section map of `α`.
`derivedSectionsMapWithCoefficients_homology` proves that its degree-`q`
map is the existing `cohomologyMapWithCoefficients f R q α`. This
follows from naturality of `homologyNatIso` and
`derivedSectionsMap_homology`. The ring `R` is fixed; this construction
changes the coefficient sheaf, not the scalar ring.

## Provenance and scope

This is an internal construction from the published
[`EtaleDerivedPullback`](EtaleDerivedPullback.md),
[`EtaleDerivedSectionsPlus`](EtaleDerivedSectionsPlus.md), and the
generic [`DerivedPlusSource`](../Cohomology/DerivedPlusSource.md).
The first provides the actual section map, exact restriction, injective
preservation and ordinary-cohomology pullback; the second provides
derived sections and the natural cohomology identifications. The generic
module constructs the required derived morphism from those data and
proves resolution independence and the homology formula. No theorem
from Harris or Berkovich is newly asserted.

The scope is ordinary derived sections of sheaves in degree zero and
etale scheme morphisms. The module does not yet prove identity or
composition laws as the scheme morphism varies, or assemble geometric
group actions in the derived category. It constructs no compact
supports, scalar extension, inverse limits, analytic-site comparison,
Galois action, or realization of Harris's Shimura spaces. These remain
separate parts of the broad framework.
