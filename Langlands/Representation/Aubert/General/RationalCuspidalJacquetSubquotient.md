# An irreducible cuspidal subquotient of a standard Jacquet module

Author: Worker 78. This is an internal consequence of published Library
constructions, prepared as a supporting unit of task
`b7887025-20b3-4c11-9fad-0e70bdf59da6`.

`IsLeviCuspidal.of_isSubquotient` proves that Levi cuspidality passes to actual
smooth subquotients when each inner unipotent subgroup is a limit of compact
subgroups. It applies `jacquet_subsingleton_of_isSubquotient` separately to
each proper standard test. This uses exactness of those Jacquet functors.

`exists_irreducible_cuspidal_jacquet_subquotient` works at the independent
universes `u` and `v` and the carrier universe `max (u + 1) v` of the rational
support-category targets. For any nontrivial actual smooth representation
`π`, it supplies an actual standard index `I` whose normalized Jacquet module
is nontrivial, and an irreducible cuspidal representation `σ` of that very Levi
which is an actual subquotient of that Jacquet module. Its premises are the
displayed standard-cocharacter, Levi-intersection, root-system, reductivity,
maximal-split-torus, generic-cocharacter and closed-unipotent/Levi premises.
It does not require compactness of a parabolic quotient, finite length,
admissibility, or an irreducible quotient of the whole Jacquet module.

The proof first uses `exists_nontrivial_isLeviCuspidal_jacquet` from
`RationalMinimalJacquet`. It applies the published
`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` to the resulting
nontrivial Jacquet module. Ambient unipotent compact-limit follows from
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
The literal inner unipotent groups inherit compact-limit from
`isLimitOfCompactSubgroups_subgroupOf`, using closedness of the chosen Levi.
The generic subquotient lemma then proves cuspidality of `σ`.

`irreducibleCuspidalJacquetSubquotient` chooses these witnesses and retains
nontriviality, irreducibility, cuspidality and the actual subquotient relation
as its certified properties. It uses classical choice.

This unit makes no claim that `π` embeds in induction of `σ`, or that `π` is a
subquotient of induction of `σ`. It does not prove support association or the
assigned irreducible Jacquet detection target. Those require a further actual
support-theoretic comparison. The provenance is entirely internal: the
minimal-Jacquet construction, the unrestricted irreducible-subquotient theorem,
the exactness/subquotient theorem, and closed-subgroup topology are reused by
Lean name. No new source translation is asserted.

The 1 local instance has module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
