# Semisimplicity of intrinsic compact-isotypic sums

This module proves the published internal proposition
`Langlands.CompactCoefficientClass.IsotypicSemisimplicityTheorem` by the theorem
`Langlands.CompactCoefficientClass.isotypicSemisimplicityTheorem`.
It imports [IsotypicSemisimplicityStatement](IsotypicSemisimplicityStatement.md)
and all its dependencies unchanged.

## Exact result and scope

For every group `G : Type uG` with a topology and every actual smooth complex
representation `A : SmoothRep.{0, uG, uV} ℂ G`, the theorem proves all three
conjuncts of the statement:

1. Each `isotypicSubrepresentation c A`, for
   `c : CompactCoefficientClass.{uG, uC} G`, is semisimple as a representation.
2. Each `selectedIsotypicSubrepresentation t A`, for a finite set of these
   classes, is semisimple as a representation.
3. `totalIsotypicSubrepresentation.{uG, uC} A` is semisimple as a representation.

The group, representative-carrier, and ambient-carrier universes remain
independent. The finite set may be empty. Semisimplicity is Mathlib's
`Representation.IsSemisimpleRepresentation`: every subrepresentation of the
displayed representation has an internal complement. This does not assert a
complement of the displayed sum in the ambient representation, or that the total
sum equals the ambient representation.

The proof needs no topological-group, separation, local-compactness,
total-disconnectedness, Haar, compact-open-cofinality, admissibility,
finite-dimension, finite-length, ambient-semisimplicity, or intrinsic-complement
assumption. The topology, smoothness, and compact coefficient property occur in
the indexed objects but supply no step in this algebraic proof.

## Implemented algebraic transfers

All helpers below are in `Langlands.CompactCoefficientClass`. The first three
work over an arbitrary field `k` and monoid `G`, with independent source and
target carrier types.

`isSemisimpleRepresentation_subrepresentation_iff` compares the actual
representation `S.toRepresentation` with the monoid-algebra submodule
`S.asSubmodule` of `ρ.asModule`. The proof constructs the subtype inclusion as
an intertwiner, converts it with
`Representation.IntertwiningMap.equivLinearMapAsModule`, and restricts its
codomain to `S.asSubmodule`. This restricted linear map is bijective: it is the
identity on underlying subtype values, with the same membership predicate.
`LinearMap.isSemisimpleModule_iff_of_bijective` transfers semisimplicity across
this map, and
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`
converts the representation condition. The module structures are thus compared
by an actual monoid-algebra linear map, rather than by identifying only the
underlying sets.

`isSemisimpleRepresentation_iSup` handles any family indexed by an arbitrary
`Type`, including an empty index type. It applies the preceding comparison and
uses `Subrepresentation.subrepresentationSubmoduleOrderIso.map_iSup` to move
the supremum into the lattice of monoid-algebra submodules. Mathlib's
`isSemisimpleModule_biSup_of_isSemisimpleModule_submodule`, applied to the full
index set, proves semisimplicity of that supremum. An explicit equality removes
the redundant full-set index before transferring back.

`isSemisimpleRepresentation_range` starts with a semisimple source
representation. The associated monoid-algebra module is semisimple. The
intertwiner's range, transported to a monoid-algebra submodule, is exactly the
range of its associated monoid-algebra linear map; the proof verifies this by
submodule extensionality. Mathlib's `IsSemisimpleModule.range` and the first
comparison helper give the required representation result. The map need not be
nonzero or injective.

## Application to the intrinsic sums

`isSemisimpleRepresentation_isotypicSubrepresentation` chooses an actual
representative `D` of the quotient class and uses the published
`isotypicSubrepresentation_eq_iSup_range` formula. Irreducibility is obtained
from `D.property.1`. Mathlib transfers irreducibility to simplicity of
`D.obj.representation.asModule`, and simple modules are semisimple. The range
helper therefore proves semisimplicity of every summand, and the supremum helper
proves semisimplicity of the isotypic part.

The final theorem applies this single-class result to its first conjunct. The
second and third conjuncts apply the supremum helper to the definitions of the
finite selected sum and total sum, respectively. No analytic projector,
annihilator, or block-isolation theorem is used.

## Provenance

This is an internal algebraic derivation of the already published statement,
not a transcription of an analytic decomposition proof. Its mathematical inputs
are the published range-and-supremum constructions and Mathlib's semisimple
module results. The explicit subtype-module comparison follows the same
construction pattern as the private atom-to-irreducibility helper in the
published [TotalCompactness](TotalCompactness.md) module; that module is not
imported. Worker 199 wrote this proof and explanation. The imported statement
was authored by Worker 199 from Worker 319's specification.
