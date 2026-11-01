# Coherent pullback on actual polarized isomorphism classes

This internal construction descends the actual `Datum.pullback` operation to
the actual quotient `Moduli`. It supplies no moduli restriction operation as
an input. All original prerequisites remain explicitly packaged in the
`Prerequisites` parameter.

The dual-map naturality, identity and composition wrappers specialize the
existing `dualAbelianBaseChangeNaturality`,
`dualAbelianBaseChangeMap_id` and
`dualAbelianBaseChangeMap_comp_pullback` results to the explicitly bundled
endpoint witnesses. Their maps are the existing actual contravariant dual
homomorphisms.

`PolarizedIso.pullbackWith` takes the actual base change of an actual
isomorphism. Its polarization equation follows by pulling back the old equation
and applying dual-comparison naturality. Ordered-section preservation follows
from `pullbackTuple_map`. `PolarizedIso.pullback` uses the derived endpoint
witnesses. `Datum.pullbackWithIso` compares arbitrary changed auxiliary
evaluations: the canonical parameter-map formula is identical, and the actual
identity of the changed abelian scheme preserves the full ordered tuple.

`Datum.pullbackIdIso` and `Datum.pullbackCompIso` use the existing actual
abelian-scheme identity and composition comparisons. The polarization equations
are precisely the specialized integral dual-valued coherence laws; the
ordered-section equations are the corresponding `LevelCoherence` results.

`Moduli.pullback` is the actual quotient map, well defined by
`PolarizedIso.pullback`. `pullback_classOf` gives its representative formula,
and `pullback_classOf_with` proves independence of any alternative auxiliary
evaluation at the changed base. Quotient induction and the actual comparison
isomorphisms prove `pullback_id` and `pullback_comp`.
`pullback_withDualWitness` also identifies restriction classes after a change
of the original datum's auxiliary evaluation, by its proved quotient equality.
