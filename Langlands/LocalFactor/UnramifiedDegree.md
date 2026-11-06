# The inertia-fixed kernel inclusion and maximal Euler degree

This is an internal algebraic prerequisite for the unramified normalization
target. It applies to the published Euler polynomial and actual
inertia-fixed monodromy kernel, over an arbitrary field and normal subgroup.
It is derived directly from those definitions and finite-dimensional linear
algebra; no local correspondence or automorphic factor assertion is assumed.

`WeilDeligneRepresentation.inertiaKernelInclusion` is the composite of the
actual invariant-subspace inclusion with the actual monodromy-kernel inclusion.
Its injectivity and rank bound are proved in the same module. The construction
uses the published `WeilDeligneRepresentation.inertiaKernelRepresentation`,
`kernelRepresentation`, and `FiniteRepresentation.invariantSubspace`.

An invertible operator has nonzero determinant, so its characteristic polynomial
has nonzero constant coefficient. Reversing that polynomial preserves its
degree. A group element acts invertibly, which identifies the degree of the WD
Euler polynomial with the dimension of its inertia-fixed monodromy kernel.

The composite of the two subtype inclusions embeds this kernel into the original
carrier. If the dimensions agree, finite-dimensional linear algebra makes that
inclusion surjective. Every vector then lies in the monodromy kernel and is fixed
by inertia. Conversely, zero monodromy and trivial inertia allow every vector to
be lifted to the kernel, so the dimensions agree. The result includes rank zero
and imposes no semisimplicity assumption.

This structural contribution does not prove the existing
`Correspondence.FullCorrespondenceUnramifiedStatement`. Its automorphic
factor comparison and principal-series clauses remain separate obligations.
