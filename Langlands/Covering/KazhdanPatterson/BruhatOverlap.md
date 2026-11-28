# Compatibility of unipotent splittings with lifted conjugation

Let \(q:W\to\mathrm{SL}_n(F)\) be a group homomorphism whose kernel is central
and killed by the natural exponent \(e\), with \(e\ne 0\) in \(F\).
For any group homomorphism \(s\) lifting the upper-unipotent subgroup along
\(q\), `unipotentLift_mul_eq_mul` proves \(s(a)w=ws(b)\) whenever
\(a q(w)=q(w)b\). The matrices \(a,b\) are upper unipotent, and \(w\) may
be any element of \(W\).

Two elements with the same image under \(q\) have equal \(e\)-th powers.
Their ratio belongs to the central kernel, so the power of the product
is the product of the powers and the ratio contributes one. The matrix
power root preserves \(a q(w)=q(w)b\) and stays upper unipotent. Transport
the roots back to the special linear group using the determinant kernel.
The lifted root of \(a\) and the conjugate of the lifted root of \(b\) have
the same image under \(q\). Taking their \(e\)-th powers gives the claimed
identity since \(s\) is a group homomorphism. Applying the power comparison
to the images of the same root under two lifts gives `unipotentLift_unique`.

`BruhatLiftData.ofCentralKernel` uses this compatibility for a supplied
homomorphic unipotent lift and normalized monomial lifts. This supplies
the overlap required by `BruhatLiftData.sectionMap`.

## Source

This is the finite-exponent argument for the overlap identity in Banks,
Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §2, Lemma 3
and equation (1), printed pp. 141–142, PDF pp. 11–12. The article uses the
positive root generators in the overlap. Literature ID
`banks-levy-sepanski-1999-block-compatible`, SHA-256
`328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`.
[DOI](https://doi.org/10.1515/crll.1999.507.131)
