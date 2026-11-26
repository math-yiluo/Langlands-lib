# Adjoint multiplicity at a σ-regular point

`adjointTracePairing` is the bilinear form
\((X,Y)\mapsto \operatorname{Tr}_{E/F}(\operatorname{tr}(XY))\).
Cyclic invariance of the matrix trace and invariance of the coefficient
trace under the algebra automorphism show that the twisted adjoint
preserves the form.

At a normalized regular norm, the adjoint fixed space is the evaluated
characteristic-polynomial algebra. For any nonzero element of this finite
reduced algebra, use its product-of-fields decomposition to choose a
multiplier whose product with the element is a nonzero idempotent. Its
evaluated matrix is a nonzero idempotent with nonzero trace in
characteristic zero. The coefficient trace multiplies this value by
\([E:F]\). This proves that the restriction of the pairing separates
fixed vectors. The conjugacy equivalence transports separation to every
σ-regular element.

The image of \(D=\operatorname{Ad}(\delta)\sigma-1\) is orthogonal to
the fixed space. If \(D^2X=0\), then \(DX\) is fixed and orthogonal to
all fixed vectors, hence \(DX=0\). Iterating yields equality of the
generalized and ordinary \(1\)-eigenspaces. Combining this with the
fixed-space dimension proves
`rootMultiplicity_twistedMatrixConj_of_sigmaRegular`.

The calculation supplies the equality at a σ-regular element in the
adjoint multiplicity argument of Arthur–Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula*, Chapter 1,
Proposition 2.2, printed pp. 11–12. Source ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
