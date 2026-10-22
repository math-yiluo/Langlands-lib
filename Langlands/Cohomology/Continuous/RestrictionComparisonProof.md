# Proof of compatibility with actual continuous restriction

Proof author: Worker 22. Worker 134 prepared this contribution, checked it
against the published dependencies, and updated this documentation.
The target statement was published in Library commit
`9173b91d7bd642075001f7d8d56e9e6d26cae822`; this proof imports it and its
dependencies unchanged by Lean module name.

`Langlands.Continuous.restrictionComparisonLaws` proves exactly the imported
`Langlands.Continuous.RestrictionComparisonLaws`, with universe parameter
`u` and without additional assumptions. All cohomology degrees are natural
numbers. Neither compactness nor invertibility of the finite-quotient
comparison is assumed; the stages use the quotient by each open normal
subgroup, even when the quotient is not finite.

For the cochain square, `finiteRestrictionCochains_comp_stage` cancels the
injective continuous-to-ordinary cochain comparison on the subgroup. The
proved naturality of that canonical comparison and the characterization
of each finite-stage map reduce the goal to ordinary cochain maps.
Their composition formula identifies both sides: the homomorphisms agree
on quotient representatives, and both coefficient morphisms preserve the
same underlying vector.

`finiteRestriction_comp_stage` applies homology to that equality.
`ShortComplex.mapHomologyIso_hom_naturality` accounts explicitly for the
homology isomorphism associated to forgetting coefficient topology. Thus
the resulting map is the existing continuous cohomology restriction.

`finiteQuotientRestriction_comp_comparison` applies colimit extensionality.
At each stage it uses the defining cocone identity for finite-quotient
restriction and the finite-stage characterization of the comparison.
The preceding homology square finishes the calculation. The final
theorem collects the three equalities into the imported proposition.

The mathematical provenance is Serre, *Local Fields* (1979), VII §5
and X §3. The proof route above is the implemented categorical calculation,
not an appeal to a source theorem as an axiom. The Lean proof is reused
unchanged from Worker 22's supplied draft. Pinned environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

