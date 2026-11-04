# Open units in actual adelic-level local factors

The proposition `Langlands.Global.AdelicLocalFactorUnitsStatement` asserts
Mathlib's `IsOpenUnits` for every factor of the already constructed
`CurvePlaceLevelFactor` and `NumberFieldLevelFactor`, at one arbitrary common
universe. All finite sets S are allowed, including the empty set. For the
curve-place construction, k and F are arbitrary fields with an algebra action
k → F. No function-field, finite-constant, perfectness or separability premise
is imposed. The number-field construction requires exactly `NumberField K`.

The curve factors are the actual completed fields at places in S and their
actual completed valuation rings at places outside S. The number-field factors
include every infinite completion, the completed fields at finite places in S,
and the completed valuation rings outside S. Their topologies are the existing
completion topologies and the existing subspace topologies, respectively.
No replacement topology is defined here.

`IsOpenUnits A` means that the map Aˣ → A is an open embedding, where the
unit group has Mathlib's topology induced by the value and inverse coordinates.
It includes both openness of the unit locus and continuity of inversion on
that locus. This is a topological property separate from the local-ring
instances already supplied by `AdelicLevelModelPoints`.

This target is a derived prerequisite for applying the published scheme-point
continuity and coefficient-change theorems to the actual arithmetic local
factors in Conrad's Theorem 3.6 (printed pp.6–8). It is not a separate quotation
or a claim of adelic transition continuity. The proof route uses the standard
fact that open subrings inherit `IsOpenUnits`: the unit map into the ambient
unit group is an embedding with open image, and composition with the ambient
unit inclusion proves the result. Mathlib supplies openness of the valuation
subrings and `IsOpenUnits` for the completed fields. This file only states the
property; its proof is a separate publication. The whole-paper transition,
descent, model-independence and global-colimit obligations remain open.
