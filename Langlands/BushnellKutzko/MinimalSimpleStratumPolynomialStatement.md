# Polynomial labels of simple strata at depth \(n-1\)

`Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialStatement`
uses one lattice-chain presentation \(L\) of a principal hereditary
order \(\mathfrak A\) in \(\operatorname{End}_F(V)\). It applies to
every nonarchimedean local field \(F\), every \(n\geq 1\), and every
prime element `π : RingPrimeElement 𝒪[F]`. The simple strata considered
have chain \(L\) and integers \(n,n-1\).

For each such stratum \(S=[\mathfrak A,n,n-1,\alpha]\),
`S.fundamentalPolynomial π` is \(\phi_\alpha\) in the polynomial ring
over \(\mathcal O_F/\operatorname{Jac}(\mathcal O_F)\). The identity
`jacobson_integer_eq_maximalIdeal` identifies this quotient with \(k_F\).
The proposition asserts that \(\phi_\alpha=f_\alpha^a\) for a positive
integer \(a\) and a monic irreducible \(f_\alpha\ne X\) of degree
dividing \(d(\mathfrak A)\). The principal chain has equal successive
layer dimensions, so \(d(\mathfrak A)=\dim_F(V)/L.\mathrm{period}\)
and the dimension sequence has least positive period \(1\).

The residue degree `elementResidueDegree F α` is \(\deg f_\alpha\).
The ramification index `elementRamificationIndex F α` is
\(L.\mathrm{period}/\gcd(L.\mathrm{period},n)\). The expression
`n.natAbs` supplies \(n\) to the natural-number gcd under \(n\geq 1\).
These invariants refer to the field \(F[\alpha]\) inside the endomorphism
algebra.

If two strata with the fixed order and integers have fundamental
polynomials that are positive powers of the same monic irreducible \(f\),
some \(u\in U(\mathfrak A)\) has \(u^{-1}\alpha_1u\) in the second coset.
At the fixed depth this is equivalence of the conjugated first stratum
with the second. This is the direction of (1.4) needed for the upper
bound on conjugacy classes.

For \(E=F[\gamma]\), the specialization takes \(E\) as the base field
with the spectral structures of `Langlands.LocalField.FiniteExtension`
and takes `LatticeChain.relativeLatticeChain` for the relative order
in \(\operatorname{End}_E(V)\). The identification of integral elements
with the spectral valuation ring uses `isIntegral_iff_mem_spectralInteger`.
The relative chain has the same lattice subsets, so their successive
indices still agree for a principal chain.

Source. C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing
conjugacy classes*, Contemp. Math. 177 (1994), 107–135.
See the layer dimensions and their period on printed p. 110, and
(1.4)–(1.5), printed pp. 112–113 (PDF pp. 123, 125–126).
The registered proceedings volume is
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
