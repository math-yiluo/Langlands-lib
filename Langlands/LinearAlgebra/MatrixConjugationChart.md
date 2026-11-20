# Local coordinates for real matrix conjugation

For a real square matrix \(C\), the image of \(X\mapsto XC-CX\) has a linear complement containing any prescribed subspace disjoint from that image. A right inverse on the image and projection along the complement give continuous linear maps \(X,Y\) with \([X(w),C]+Y(w)=w\). On the prescribed subspace, \(X\) is zero and \(Y\) is the identity.

`affineMatrixConjugation` sends \(w\) to \((1+X(w))(C+Y(w))(1+X(w))^{-1}\) wherever \(1+X(w)\) is invertible, using the ring inverse for the ambient formula. It is smooth on this open locus. Differentiation at zero gives the identity by the splitting equation. The inverse function theorem gives a local coordinate chart taking zero to \(C\). Shrinking to the open set where the derivative is invertible gives smoothness of both chart directions on their domains.

This is an internal construction from finite-dimensional linear algebra, differentiation of matrix multiplication and inversion, and the smooth inverse function theorem.
