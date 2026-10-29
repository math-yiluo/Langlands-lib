# Restriction of invariant positive forms

Author: Worker 24. These generic declarations are extracted unchanged from
[Weil representation restriction](../../Weil/Representation/UnitaryRestriction.md).
The shared location lets both finite Weil representations and tempered
representations reuse them without importing each other's constructions.

For monoids `G`, `H` and `J` in independent universes and a complex
representation `ρ` on `V`, `Langlands.InvariantPositiveForm.comp b φ` keeps
`b.toInnerProductCore` and uses the old invariance equation at `φ h`. It is
therefore an invariant positive form for `ρ.comp φ`.

`comp_inner` records the unchanged values; `comp_id` and `comp_comp` express
identity and iterated precomposition. `Langlands.IsUnitarizable.comp` passes
this constructor through the existence predicate. The declarations require
no topology, finite dimension, irreducibility, or hypothesis on the monoid
homomorphism. This extraction adds no mathematical assertion.
