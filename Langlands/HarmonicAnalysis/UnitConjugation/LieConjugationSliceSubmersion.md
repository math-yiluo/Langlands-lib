# Submersion for conjugation from a Lie algebra slice

Let \(A\) be a normed finite-dimensional associative algebra over a complete
nontrivially normed field \(F\), and let \(B\) be an \(F\)-subalgebra.
`LieConjugationSliceSubmersionStatement` asserts that the map
\((g,X)\mapsto gXg^{-1}\) from \(A^\times\times U\) to \(A\) is open if
\(U\) is open in \(B\) and \(B+\operatorname{im}(\operatorname{ad}X)=A\)
holds for each \(X\in U\). The field and algebra universes are independent.
The range of this map is the ambient conjugation saturation of \(U\).

In ambient coordinates for the unit, multiplication and inversion give
the strict differential at \((1,X)\) as \((a,b)\mapsto aX+b-Xa\).
The span condition gives surjectivity by decomposing each \(z\in A\) as
a slice direction plus a commutator. Left translation of the unit and
conjugation on the output carry the strict differential to a general
\((g,X)\). To prove local openness, restrict along an affine map through
the base point with linear part a continuous right inverse of the
differential. The composite has the identity strict differential, so
the inverse function theorem shows that the image of each neighborhood
of the base point contains a neighborhood of its image. The unit chart
and the inclusion of \(U\) are open embeddings.

This is the submersion used in Harish-Chandra, *Admissible invariant
distributions on reductive p-adic groups* (AMS, 1999), proof of
Corollary 2.3, printed pp. 14–15. On a semisimple centralizer slice the
span condition follows from invertibility of the adjoint action on the
complement of the centralizer.
