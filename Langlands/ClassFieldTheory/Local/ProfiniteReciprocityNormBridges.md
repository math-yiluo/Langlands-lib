# Norm-kernel bridges for the profinite reciprocity completion

Worker 1607 authors these internal, derived constructions for the existing
`ProfiniteReciprocityCompletion` target. The arithmetic propositions
`NormSubgroupExistence` and `NormSubgroupsSeparatePoints` remain explicit
premises here. This module establishes the structural consequences of those
premises and the existing finite norm-residue relation.

`FiniteAbelianExtension.ofIntermediateField` packages an actual intermediate
field that is finite and abelian Galois into the Library's existing finite
abelian extension type. Its field, algebra structure and determinant norm are
unchanged.

`finiteReciprocityQuotientDescent` treats an open finite quotient whose kernel
is the norm subgroup of such an extension. Restriction from the actual
absolute-Galois abelianization lands in the finite Galois group. The inverse
of `finiteNormResidueEquiv` then lands in the actual norm quotient, and the
identity on field units induces a continuous map to the given finite
quotient. The representative formula for the finite norm-residue equivalence
proves that this composite agrees with the original quotient projection
after the supplied reciprocity map.

`normSubgroupExistence_for_topology` compares the supplied topology and the
canonical topology by their already proved equality with the module
topology. The arithmetic existence premise therefore applies to each open
finite quotient for the supplied topology. The resulting intermediate field
is packaged as above, and the exact norm-kernel relation gives the required
descent. No continuity is deduced from an abstract finite-index quotient:
openness is part of the quotient data and all quotient maps use their
quotient topologies.

`injective_of_normSubgroupsSeparatePoints` tests an element in the kernel
against each finite restriction. If the element is nonidentity, the
arithmetic separation premise supplies a norm group that excludes it.
The exact finite norm-kernel relation puts it in that same group, a
contradiction.

These are formal deductions from the imported published constructions and
the explicitly retained arithmetic premises, rather than new
original-source assertions. They neither establish arithmetic norm
existence or separation nor assume any completion comparison.
