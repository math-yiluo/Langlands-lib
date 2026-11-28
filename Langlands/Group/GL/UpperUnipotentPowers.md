# Roots of upper-unipotent matrices

`upperUnipotentPowerRoot` constructs an upper-unipotent matrix of the same size
as its input. If the natural exponent \(e\) is nonzero in the field, then
`upperUnipotentPowerRoot_pow` proves that the \(e\)-th power is the input. This
includes both characteristic zero and positive characteristic prime to \(e\).

Write the input as \(1+Z\) with \(Z\) strictly upper triangular. In the identity
\((1+X)^e=1+eX+R_e(X)\), the remainder \(R_e\) contains only terms of degree at
least two in \(X\). The implementation evaluates it recursively using
\(R_{k+1}=R_k+(kX+R_k)X\). If two strictly upper triangular matrices agree
through a given superdiagonal, their remainders agree through the next one
by `UpperUnipotentFactorization.agreeBelow_mul`. Iterating
\(X\mapsto e^{-1}(Z-R_e(X))\) from zero therefore reaches a fixed point in at
most the matrix size. The resulting matrix \(1+X\) is upper triangular with
unit diagonal, so it has determinant one.

The recursion preserves an intertwining equation \(AM=MB\) because it uses
addition, multiplication, the identity, and field scalars. The lemma
`upperUnipotentPowerRoot_mul_eq_mul` applies this to two upper-unipotent
matrices and an invertible \(M\). In particular, an upper-unipotent group and
any of its conjugates have \(e\)-divisible intersection when \(e\) is nonzero
in the field.

## Source

The power construction supplies the divisibility used in a finite-exponent
approach to the overlap identity in Banks, Levy, and Sepanski,
*Block-compatible metaplectic cocycles*, §2, Lemma 3 and equation (1), printed
pp. 141–142, PDF pp. 11–12. The article proves the identity using root
generators. Literature ID `banks-levy-sepanski-1999-block-compatible`,
SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`.
[DOI](https://doi.org/10.1515/crll.1999.507.131)
