# Cyclic directions and centralizer orbit closure

For real square matrices \(A\) and \(D\) and a real column vector \(v\),
`cyclicVectorLinePolynomial A D v` takes the determinant of the cyclic-vector
columns of the polynomial matrix \(A+XD\). Evaluation at \(t\) gives the
determinant for the matrix \(A+tD\) and the same vector \(v\). If \(A+D\) has
a cyclic vector, this polynomial is nonzero for a choice of \(v\). The finite
set of its nonzero real roots is closed and avoids zero, so \(A+tD\) is
cyclic throughout a sufficiently small punctured neighborhood of zero.

The closure result fixes a real matrix \(C\) and an invertible matrix \(q\)
with \(qCq^{-1}=C^t\). It assumes \(A\) and \(D\) commute with \(C\) and
\(A+C+D\) has a cyclic vector. Put \(L(t)=A+tD\). For small nonzero \(t\),
one matrix \(a\) simultaneously conjugates \(L(t)+C\) and \(C\) to their
transposes. Thus \(q^{-1}a\) centralizes \(C\) and conjugates \(L(t)\) to
\(q^{-1}L(t)^tq\), after subtracting \(C\). Taking the limit at zero places
\((A,q^{-1}A^tq)\) in the closure of the centralizer-conjugacy pairs whose
first component lies in any specified set containing the line. Consequently
any continuous function into a Hausdorff space that is centralizer-invariant
on this set takes the same values on \(A\) and \(q^{-1}A^tq\).

This is an internal geometric lemma derived from the cyclic commuting-pair
transposition lemma. The shift by \(C\) allows the cyclic witness to lie in
a translate of the prescribed line.
