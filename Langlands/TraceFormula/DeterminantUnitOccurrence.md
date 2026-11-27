# A twist intertwiner from occurrence on the determinant-unit subgroup

`exists_twist_intertwiner_of_cyclicKernel` is an algebraic lemma for the
cyclic quotient that arises from determinant valuation. It takes a
surjection onto the additive integers, written multiplicatively, and
representations on independent complex vector spaces. Assume a nonzero
intertwiner on the kernel and a positive-degree element acting by nonzero
scalars on both carriers.

Conjugation acts on the space of linear maps between the representations.
The kernel fixes the supplied intertwiner and all its translates. The
positive-degree scalar element acts on it by the ratio of the two scalars.
A lift of the generator of the integers therefore preserves the finite span
of the initial translates, since the next translate is a scalar multiple
of the original map. An eigenline in that span is stable under the kernel
and the generator. The associated character descends to the integer
quotient and makes the nonzero eigenvector a full-group intertwiner from
the corresponding twist.

This is an internal consequence of the published cyclic-quotient
eigenline construction.

`exists_unramifiedDeterminantTwist_intertwiner` applies the cyclic quotient
lemma to the actual completion valuation composed with the determinant. For
positive rank, the determinant and the valuation on units are surjective.
Degree is the integer coordinate of the multiplicative valuation. A
uniformizer has valuation `WithZero.exp (-1)`, so its inverse has degree
\(+1\). The proof chooses a field unit of degree \(+1\) by surjectivity.
The associated scalar matrix in \(\mathrm{GL}_n\) has determinant of degree
\(+n\) because its determinant is the \(n\)-th power of the scalar. This
matrix acts by a scalar in the source by admissible Schur and in the target
by hypothesis. Pulling the integer character back to the field units gives
exactly a character trivial on valuation-one units. Both the old and the
new intertwiners have the same carriers.
