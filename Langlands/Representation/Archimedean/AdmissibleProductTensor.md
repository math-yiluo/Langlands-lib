# Algebraic multiplicity tensors from admissible coordinate families

For a complex vector space \(V\) and an arbitrary index type \(I\), the
evaluation map sends \(v\otimes c\) to the family \(i\mapsto c(i)v\), where
\(c\) is any scalar family on \(I\). It is injective. A basis of \(V\)
identifies each algebraic tensor with finitely supported scalar families.
Evaluating each vector coordinate recovers those scalar families.

A family whose values span a finite-dimensional space lies in the range of
evaluation. Choose a basis of the span and take the finite sum of its basis
vectors tensored with the coordinate functions on \(I\).
`toMultiplicityTensor` uses the inverse to the evaluation map on its range
to lift a linear family of coordinates with this finite-span property.
The lift preserves injectivity of the family map. If a source operator
intertwines coordinatewise with an endomorphism of \(V\), its tensor action
uses that endomorphism on \(V\) and the identity on the scalar family
space.

`finiteDimensional_span_range_of_compactCoordinates` establishes the
finite-span property under the compact representation hypotheses used at
an archimedean place. A compact-finite source vector lies in its
finite-dimensional orbit span. With weak continuity of its compact
representation, the matrices on that orbit span form a continuous
finite-dimensional representation. Each coordinate restricts to an
intertwiner from this single matrix representation. By admissibility of
the target, these intertwiners lie in a finite-dimensional space.
Evaluating that space at the given vector yields a finite-dimensional
subspace containing all coordinates, including when \(I\) is infinite.

This internal construction uses the matrix and continuity comparison in
[`KFiniteDual`](../KFiniteDual.md), the Library's
[`IsAdmissibleGKModule`](GKModule.md), and Mathlib's
`TensorProduct.piScalarRightHom` and `TensorProduct.equivFinsuppOfBasisLeft`.
It turns equivariant coordinates in copies of a local admissible standard
module into the multiplicity tensor used for single-place subquotient
extraction.
