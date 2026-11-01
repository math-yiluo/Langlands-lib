# Derived representation-valued sections of actual small-etale transport sheaves

This internal construction derives the actual section representation functor
of `EtaleTransportSections`, using the abelian structure and enough injectives
constructed in `EtaleTransportAbelian`. The inputs are a scheme
`Y : Scheme.{u}`, a group `G : Type w`, a homomorphism
`ρ : G →* (Aut Y)ᵐᵒᵖ`, the explicit hypothesis `Small.{u} G`, and a
commutative ring `R : Type u`. Module carriers are in universe `u`.
The given scheme and group universes remain independent.

`cohomology ρ R q` is the classical right derived functor of
`sectionRepresentation ρ R`, with values in `Rep.{u} R G`.
`complex` applies sections termwise to a chosen injective resolution
in the actual module transport-sheaf category. `homotopyFunctor` makes
this construction functorial in the homotopy category, and `complexIso`
identifies its objects with the chosen complexes. For every injective
resolution in that category, `cohomologyResolutionIso` computes
representation-valued cohomology as homology of its section complex.
Left exactness gives `cohomologyZeroIso`; positive-degree cohomology
vanishes on injective transport sheaves.

The bounded-below constructions explicitly assume
`HasDerivedCategory.{wS}` for the transport-sheaf category and
`HasDerivedCategory.{wT}` for the representation category, with independent
localization universes. These are Mathlib's derived-category availability
hypotheses. They do not supply a desired cohomology object or comparison.

`rightDerivedFunctor` is Mathlib's actual right derived functor
from the bounded-below derived category of transport sheaves to
`DerivedCategory.Plus (Rep.{u} R G)`. `derivedSections` first places
a sheaf in degree zero and then applies this functor. The target is
the derived category of representations; the construction starts with
the strict representation-valued section functor and injective
resolutions in its actual sheaf source.

`complexPlus` is a bounded-below representation complex. It extends
the chosen nonnegative injective resolution by zero to integer degrees,
then applies the section representation functor. `resolutionIso`
identifies the derived object with the localization of this construction
using any injective resolution; `complexPlusIso` selects the chosen one.
`complexPlusMap` applies sections to Mathlib's chosen compatible
resolution lift of a coefficient map. The strict choices are not asserted
to satisfy functor laws before localization. The two naturality equations
identify their localized maps with the functorial derived-section maps,
including the more general equation for any compatible resolution map.

`homologyNatIso` naturally identifies nonnegative cohomology of
`derivedSections` with `cohomology`. Its component can be computed from
any transport injective resolution. `homologyZeroIso` recovers actual
section representations; negative cohomology vanishes. `diagramFunctor`
postcomposes arbitrary coefficient diagrams and their natural
transformations with the actual derived-section functor. Its indexing
object and morphism universes are independent.

The provenance is internal specialization of Mathlib's right derived
functors and the Library's `Langlands/Cohomology/DerivedPlus.lean` and
`DerivedPlusNaturality.lean` to the genuine transport sheaf category and
its constructed section representation functor. The ordinary model is
`EtaleDerivedSectionsPlus`; the topological representation-valued model
is `EquivariantDerivedSections`. All comparison and naturality proofs
apply the generic constructions with these concrete source and target
categories. No new result is attributed to Harris or Berkovich.

The representations here are algebraic. This unit does not prove that
forgetting the derived action recovers ordinary small-etale derived
sections of the restricted sheaf: that comparison needs a separate
acyclicity or exactness argument. Smoothness, compact supports, analytic
geometry, arithmetic coefficients, level towers and Harris
specialization also remain separate obligations.
