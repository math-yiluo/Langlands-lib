# The Bruhat section from unipotent and monomial lifts

For \(G=\mathrm{SL}_n(F)\), `slUpperUnipotent` is the upper-unipotent subgroup \(N\), pulled back from the general linear group. `IsSpecialLinearMonomial` describes the determinant-one monomial matrices \(M\) using the permutation support and unit entry in each column.

`BruhatFactors` records a factorization \(g=a m b\) with \(a,b\in N\) and \(m\in M\). The Library's monomial double-coset coordinates give a factorization in \(\mathrm{GL}_n(F)\). The upper-unipotent factors have determinant one by the triangular determinant formula. Hence \(m\) has determinant one as well. The proof transports the factors along the identification of \(\mathrm{SL}_n(F)\) with the determinant kernel. The uniqueness of \(m\) follows from injectivity of the monomial double-coset coordinates.

For a group homomorphism \(q:W\to G\), `BruhatLiftData` supplies a homomorphic lift \(s_N\) and a normalized monomial lift \(s_M\). The overlap identity says that \(s_N(a)s_M(m)=s_M(m)s_N(b)\) whenever \(a m=m b\). With these data, `BruhatLiftData.sectionMap` constructs a normalized section \(s_G\) of \(q\). Its value on \(g=a m b\) is \(s_N(a)s_M(m)s_N(b)\).

If \(a m b=a' m' b'\), injectivity of the double-coset coordinates gives \(m=m'\). The equality in \(G\) also gives \((a')^{-1} a m=m b' b^{-1}\). Applying the overlap identity and multiplying by the outer lift factors proves that the section value is independent of the factorization. The identity factorization gives normalization. Applying \(q\) to the three lifts gives \(g\). The arithmetic construction uses monomial lifts from the chosen torus and Weyl representatives and verifies the overlap identity with the root relations.

## Source

- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §2, Lemma 3 and equation (1), printed pp. 141–142, PDF pp. 11–12. In §3, printed p. 145, PDF p. 15, the type A specialization uses the determinant-one monomial subgroup of the general linear group. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
