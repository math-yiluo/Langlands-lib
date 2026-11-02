# Restricting fppf sheaves to the big etale topology

This internal construction compares Mathlib's existing big topologies. Every
etale morphism is flat and locally of finite presentation. Consequently every
jointly surjective etale covering family is an fppf covering family.
`etalePrecoverage_le_fppfPrecoverage` formalizes this inclusion using
`Scheme.precoverage_mono`, and `etaleTopology_le_fppfTopology` applies the
monotonicity of the generated Grothendieck topology.

`etaleTopologyOver_le_fppfTopologyOver` gives the same inclusion on `Over S`
for every scheme `S`. Both slice topologies test a sieve through the same
`Sieve.overEquiv`, so their comparison follows directly from the big-site
comparison. No restriction on the test schemes is imposed.

`fppfSheafToEtaleSheaf S A` restricts a sheaf with values in any category `A`
along this inclusion. Its underlying presheaf and every underlying natural
transformation are unchanged; its sheaf condition follows from
`Presheaf.IsSheaf.of_le`. The two final equations record these identities.

This construction supplies no converse sheaf condition. In particular it does
not assert that an etale sheafification is an fppf sheaf, that etale and fppf
Picard sheafifications agree, or that either Picard sheaf is representable.
Its provenance is the listed Mathlib constructions and the etale-to-flat and
etale-to-locally-finite-presentation instances, rather than a separate
literature assertion.
