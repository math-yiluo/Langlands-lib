# Trace duality for lattice-chain filtrations

This module develops the algebraic form of the lattice pairing used in
Bushnell–Kutzko 1993, (1.1.4) and (1.3.6), printed pp. 22 and 29
(`bushnell-kutzko-1993-admissible-dual-gln`). The coefficient field is
the fraction field of a discrete valuation ring. A finite submodule is
separated from an exterior point by a linear form with values in the maximal
ideal on the submodule. The definition `maximalIdealInField` takes the image
of the maximal ideal under the map from the ring to the field.

For a lattice chain, `mem_endFiltration_iff_trace_mul` identifies the trace
dual of the step of index \(n\) with the step of index \(1-n\). The trace
test is membership in `maximalIdealInField`. An endomorphism of depth one
induces a nilpotent matrix on a lattice reduced modulo the maximal ideal,
so its trace satisfies this test. For the converse, a vector sent outside
the requisite lattice can be detected by a separating linear form. The
resulting rank-one endomorphism lies in the test filtration step by
periodicity of the chain. The module also proves finite generation of each
endomorphism filtration step.
