# Available data for the Levi part of a special compact subgroup

`Langlands.BruhatTits.SpecialCompact.availableSpecialLeviCompact` proves
`AvailableSpecialLeviCompactStatement.{u}` at arbitrary universe `u`.
For every valid corrected KP assignment, ambient special apartment vertex,
generic cocharacter and subset of its simple relative roots, it supplies
available data for the actual standard Levi at the same torus and a special
vertex whose special compact subgroup equals the preimage of the ambient
special compact subgroup under the actual Levi inclusion on rational points.

## Implemented proof

The published `standardLevi_isConnectedReductive` provides reductivity of the
actual standard Levi. The published `validAssignmentTorusRebasing` constructs
a valid assignment whose Levi datum uses precisely the ambient torus and
`Standard.leviTorusHom`; validity implies availability for that Levi.
`KPBuildingAssignment.IsValid.isAvailableFor` also supplies availability for
the original ambient datum.

The private helper `exists_specialCompactLevi_witness` eliminates the equality
of the torus and heterogeneous equality of its inclusion. It applies the
published `prescribedLeviSpecialVertex` to obtain a special vertex in the
prescribed omega-compatible Levi apartment, with literal valuation
restriction from the original ambient special point. The required ordinary
root direction coverage is the `derivativeRoots_affineRoots` field of the
ambient apartment axioms, obtained from availability. The ambient generic
cocharacter remains generic for the Levi by `relativeRoots_subset_of_factor`.

The published `Iwasawa.availableIwasawa` gives compact-open maximality for
both the ambient special compact subgroup and the special compact subgroup
of the available Levi datum. The published
`standardLeviSpecialCompactSubgroup_le` puts this Levi subgroup inside the
preimage of the ambient compact subgroup. The latter preimage is compact
by `RenardCartan.isCompact_specialCompactLeviSubgroup`, since the actual Levi
is closed. Maximality of the Levi special compact subgroup gives the reverse
inclusion, hence exact equality.

## Provenance and scope

This is a derived composition of the named published Library results for
the unchanged statement. The prescribed-vertex construction implements the
Levi apartment restriction and special-point comparison, and rebasing
supplies the required assignment. The proof establishes the assignment-level
geometric formulation associated with Renard V.5.1(5) in the target's
Markdown; it does not assert the full list of properties in that source.

The sole building premise is the given assignment's full corrected
`IsValid` predicate. Every auxiliary proposition used here is discharged by
a published proof. The theorem imposes no restriction on characteristic,
residue characteristic, rank, splitness, quasi-splitness or ramification,
and makes no assumption that a valid assignment exists.
