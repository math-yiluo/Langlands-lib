# Monomorphisms from groups of multiplicative type are detected on fibres

`Langlands.GroupScheme.multiplicativeTypeMonomorphismSpreading` proves the
published `MultiplicativeTypeMonomorphismSpreadingStatement` in every
universe. Its two clauses formalize SGA 3, Exposé IX, Corollaries 6.6 and
6.7 (Gille–Polo recomposed edition, pp. 54–55, original margins 66–67,
registered as `sga3-expose-ix-gille-polo-2009`).

For the local clause, the separated target makes the full scheme-theoretic
kernel a closed subgroup of the source. The source's multiplicative-type
geometry gives affineness of this kernel. Local finite presentation of
the kernel follows from the corresponding source property and the
target or base hypothesis through `locallyOfFinitePresentation_kernel_of_source`.
The kernel–monomorphism equivalence identifies the residue-field kernel
with the unit group. The finite-fibre neighbourhood lemma yields an open
neighbourhood where the kernel is locally quasi-finite.

The supporting theorem
`RelativeMultiplicativeType.IsMultiplicativeType.isFinite_of_locallyQuasiFinite_closedSubgroup`
proves finiteness there by the valuative criterion. In each valuative
square the pullback of the subgroup to the fraction field is finite,
since it is locally quasi-finite and quasi-compact over a field.
`finiteGroupSchemeUniformExponent` provides a positive exponent for the
point over the fraction field. The point therefore factors through the corresponding
torsion of the ambient group, which is finite by
`IsMultiplicativeType.torsion_geometry`. The valuative criterion for that
finite morphism extends the point over the valuation ring. The fraction-field spectrum is schematically
dominant in the valuation-ring spectrum, so the extension factors through
the closed subgroup. This proves universal closedness of the subgroup
structure morphism. Together with affineness and local finite type, this
gives finiteness. This is a derived valuative argument using the published
finite torsion and field exponent theorems.

The finite-unit-fibre lemma now shrinks the neighbourhood to one where
the kernel is the unit group. Kernel base change and the kernel–monomorphism
equivalence give the claimed monomorphism on that open.

For the global clause, local finite presentation of the source and
the base or target hypothesis supply the inputs to
`mono_of_residueField_fibres`. That theorem proves triviality of the full
kernel from the triviality of all its residue-field fibres, with no
separatedness hypothesis on the target.
