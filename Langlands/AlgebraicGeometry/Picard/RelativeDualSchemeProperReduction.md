# Conditional properness assembly for the chosen dual

This internal derived module defines the proof-input record
`Langlands.AbelianScheme.RelativeDualSchemeProperInputs.{u} : Prop`.
Its three fields are proofs of:

- `RelativeDualSchemeFinitePresentationStatement.{u}`;
- `RelativeDualSchemeQuasiCompactStatement.{u}`;
- `RelativeDualSchemeValuativeExistenceStatement.{u}`.

The conditional theorem
`Langlands.AbelianScheme.relativeDualSchemeProper_of_prerequisites` takes
this record as its sole premise and proves the published proposition
`Langlands.AbelianScheme.RelativeDualSchemeProperStatement.{u}`.
No inhabitant of the input record is constructed in this module.

All three fields concern the existing structural morphism
`(dualScheme A hA).hom`, for every quasi-separated base `S : Scheme.{u}`,
every `A : AbelianScheme S` and every `hA : HasDualScheme A`.
The assembly keeps the universe and all these quantifiers unchanged.
It does not prove any of the three input statements, and it is not an
unconditional proof of properness.

For fixed `S`, `A` and `hA`, the construction obtains separatedness from the
published theorem `relativeDualSchemeSeparated`. It installs the supplied
local finite presentation and quasi-compactness fields as local instances.
Mathlib infers local finite type from local finite presentation.
`UniversallyClosed.of_valuativeCriterion` then supplies universal
closedness from quasi-compactness and the supplied valuative existence.
These are precisely the three parent properties of Mathlib's `IsProper`:
separatedness, universal closedness and local finite type.

The provenance is the formal assembly of the imported Library statements,
the published separatedness proof and Mathlib's valuative criterion.
No new comparison with a literature representer is asserted. In particular,
this helper does not identify geometric point sets with a representing
functor or infer properness from field geometry. It does not construct a
dual, and it uses neither the parent relative geometry target nor any
additional geometric hypothesis on the chosen parameter scheme.
