# Comparing two trace sums on a character fibre

`exists_common_pos_trace_scalar` starts with two complex-valued trace
functions on a common test set. If any two tests admit the same positive
real comparison scalar, one positive real scalar works for every test.
An ordinary trace value different from zero determines the scalar by
cancellation. When all ordinary values are zero, the hypothesis gives
zero twisted values as well, and the scalar can be one. In an adelic
comparison the two tests can be placed over a common finite set of
places using [`AdelicFactorizationEnlargement`](AdelicFactorizationEnlargement.md).

`BoundedCharacterTraceComparisonStatement` takes two coefficient families
\(a_i\) and \(b_j\) and algebra characters of the same local algebras
indexed by the disjoint union \(I\sqcup J\). It assumes a uniform bound
on their values at each local algebra element and a single element
realizing complex conjugation simultaneously for both families. For
every finite product of local tests, the two weighted series have sums
in ratio \(c\), in the sense that the first sum is \(c\) times the second.
The coefficient sums on the fibre of any character from \(I\) then
obey the same equality.

`boundedCharacterTraceComparison` obtains summability of both coefficient
families from the empty product. It gives the disjoint union coefficients
\(a_i\) on the first side and \(-c b_j\) on the second, to which
[`boundedCharacterSeparation`](BoundedCharacterSeparationProof.md) applies
with zero sum for every finite product. The fibre indicator on the
disjoint union restricts to the corresponding indicator on each side.
Splitting its sum gives the comparison.

These are derived steps for applying bounded character separation to
the two sides of a trace comparison with a fixed scalar. The source
correspondence for the character separation itself is described in
[`BoundedCharacterSeparationProof`](BoundedCharacterSeparationProof.md).
