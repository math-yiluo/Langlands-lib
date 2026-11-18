# Assembly of multiplicative-type monomorphism spreading

Worker 878, using the global fibre criterion of Worker 677, relative
multiplicative-type geometry of Worker 879, and the finite-subgroup reduction
of Workers 877 and 887.

`multiplicativeTypeMonomorphismNeighbourhoodOfFiniteSubgroupSpreading`
constructs a `MonomorphismNeighbourhood f s` with an open set containing
the specified base point and a proof that the restriction is a monomorphism.
Its assumptions are exactly those of the local assertion of
`MultiplicativeTypeMonomorphismSpreadingStatement`, with the
finite-subgroup spreading proposition supplied as an additional premise.
Relative multiplicative type supplies the affine and locally finitely
presented source needed by the published kernel reduction.

`multiplicativeType_mono_of_residueField_fibres` proves the global assertion
6.7 under its original hypotheses, without separatedness of the target.
To apply `mono_of_residueField_fibres`, the proof uses relative
multiplicative type to obtain local finite presentation of the source.
Local finite presentation of the target implies local finite type, giving
the required disjunction with local noetherianity of the base.

`multiplicativeType_monomorphismSpreading_of_finiteSubgroupSpreading`
proves both clauses of `MultiplicativeTypeMonomorphismSpreadingStatement` from
`MultiplicativeTypeFiniteSubgroupSpreadingStatement`. For the local
clause it extracts the open set and the two certificates from the chosen
neighbourhood. For the global clause it uses the preceding
fibre criterion. All schemes, group schemes, homomorphisms and base
points retain the quantifiers of the imported target in every universe.

`multiplicativeType_monomorphismSpreading_of_uniformExponent` composes this
result with the published
`FiniteSubgroupSpreadingReduction.finiteSubgroupSpreading_of_uniformExponent`.
Its sole mathematical premise is
`QuasiFiniteCommutativeUniformExponentStatement`, which remains to be proved
for this route to give the unconditional local assertion.

These constructions and implications are derived internal composites of
the imported APIs. The kernel and finite-subgroup reductions explain the
route corresponding to SGA 3 IX 6.6. The unit-section fibre criterion in
`Langlands.GroupScheme.FiberwiseMonomorphism` supplies the global argument
for 6.7.
