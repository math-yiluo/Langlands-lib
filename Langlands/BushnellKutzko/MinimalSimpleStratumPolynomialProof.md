# Polynomial labels of simple strata at depth \(n-1\): proof

The module `Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialProof` proves the Library
statement `Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialStatement`:

```lean
theorem Langlands.BushnellKutzko.minimalSimpleStratumPolynomial :
    MinimalSimpleStratumPolynomialStatement.{uF, uV}
```

For a principal lattice chain \(L\) of period \(e\) over a nonarchimedean local field \(F\), an
integer \(n\ge 1\) and a prime element \(\pi\), it proves both clauses: every simple stratum
\(S=[\mathfrak A,n,n-1,b]\) on \(L\) has `S.fundamentalPolynomial π` \(=f^a\) with \(f\) monic,
irreducible, \(f\ne X\), \(a>0\), \(\deg f\mid N/e\), `elementResidueDegree F b` \(=\deg f\) and
`elementRamificationIndex F b` \(=e/\gcd(e,n)\); and two such strata whose fundamental polynomials
are positive powers of the same monic irreducible \(f\) satisfy \(u^{-1}b_1u\in b_2+\mathfrak
P^{1-n}\) for some \(u\in U(\mathfrak A)\).

## Helper declarations of this module

- `subfieldIntegers_isLocalHom`: `algebraMap 𝒪_F (subfieldIntegers F E)` is a local
  homomorphism (Mathlib's `Algebra.IsIntegral.isLocalHom`).
- `adjoin_elementAlgebra_generator`: the element \(b\) generates `elementAlgebra b` over \(F\).
- `eq_of_pow_eq_pow_of_irreducible`: over a field, \(f^a=p^m\) with \(f,p\) monic irreducible and
  \(a>0\) forces \(f=p\).
- `LatticeChain.fieldShift_fundamentalUnit`: if \(\beta\) shifts the chain by \(-n\), then
  \(\pi^{n/g}\beta^{e/g}\), \(g=\gcd(e,n)\), has shift zero.
- `LatticeChain.isMinimalOver_of_criticalExponent_lt`: a generator \(\beta\) with
  \(v_{\mathfrak A}(\beta)=-n\) and critical exponent below \(1-n\) is minimal. If \(\beta\notin F\),
  `minimalCriticalExponent` (BK93 (1.4.15)) gives \(v_{\mathfrak A}(\beta)\le k_0\) with equality
  exactly for minimal \(\beta\), and \(k_0<1-n\) forces equality; if \(\beta\in F\),
  `LatticeChain.isMinimalOver_of_mem_range` applies.
- `LatticeChain.stabilizerLayerEquiv_fundamentalUnit`: on each layer, the layer map of
  \(P^{n/g}B^{e/g}\) for \(P\) the uniformizer and \(B\) the unit \(\beta\) is multiplication by the
  residue of the integral unit \(w=\pi^{n/g}\beta^{e/g}\) (`subfieldLayerEquiv_integerUnit`).
- `LatticeChain.exists_unitFiltration_conj_of_minpoly_eq`: for two normalizing fields with
  generators \(\beta_1,\beta_2\) of shift \(-n\), whose units \(w_j=\pi^{n/g}\beta_j^{e/g}\) have
  residues with the same minimal polynomial over \(k_F\), there is \(u\in U(\mathfrak A)\) with
  \(u^{-1}\beta_1u-\beta_2\in\mathfrak P^{1-n}\). The layer automorphisms of
  `exists_layerEquiv_residue_intertwine` satisfy the hypothesis of `exists_layer_intertwiner`
  with \(P\) the uniformizer and \(B_j=\beta_j\), and `exists_unitFiltration_conj_sub_mem` lifts
  the resulting family.
- `subfieldEmbedding_baseIntegerUnit_zpow_mul` and
  `fundamentalPolynomial_eq_reduceIntegralPolynomial`: the fundamental element
  `S.fundamentalElement π` is the image of the integral unit \(w\), so `S.fundamentalPolynomial π`
  is the reduced characteristic polynomial of \(w\).
- `exists_simpleStratum_minimal`: a simple stratum with chain \(L\) and integers \(n,n-1\) gives
  the field `elementAlgebra S.b`, its normalizing hypothesis on \(L\), and the unit \(b\) of shift
  \(-n\), which is minimal and maps to `S.b`. The shift comes from `valuation_eq_shift` and the
  minimality from `isMinimalOver_of_criticalExponent_lt`, since `IsSimple` at depth \(n-1\) says
  that the critical exponent is below \(-(n-1)\).

## Route of the proof of the first clause

Let \(E=F[b]\), \(\beta=b\in E^\times\) and \(w\in\mathfrak o_E^\times\) the unit
\(\pi^{n/g}\beta^{e/g}\) (`exists_integerUnit_of_fieldShift_zero`), with residue \(c\in k_E\).

1. `reduceIntegralPolynomial_charpoly_eq_minpoly_pow` gives
   `S.fundamentalPolynomial π` \(=f^m\) with \(f\) the minimal polynomial of \(c\) over \(k_F\),
   transported to \(\mathcal O_F/\operatorname{Jac}(\mathcal O_F)\) by `residueJacobsonEquiv`. It is
   monic and irreducible, and \(f\ne X\) because \(c\ne 0\).
2. `ramificationIndex_and_residue_adjoin_of_isMinimalOver` gives \(e(E|F)=e/g\) and that \(c\)
   generates \(k_E\); then \(\deg f=[k_E:k_F]\) (`natDegree_minpoly_eq_finrank_of_adjoin_eq_top`)
   equals `subfieldResidueDegree F E` (`subfieldResidueDegree_eq_finrank`). These are the values
   of `elementRamificationIndex` and `elementResidueDegree`, since `F[b]` is a field.
3. `finrank_residueField_dvd_of_isPrincipal` gives \([k_E:k_F]\mid N/e\).

## Route of the proof of the second clause

For \(S_1,S_2\) with \(\phi_{S_j}=f^{a_j}\), step 1 gives \(\phi_{S_j}=f_j^{m_j}\) with \(f_j\) the
transported minimal polynomial of the residue \(c_j\); `eq_of_pow_eq_pow_of_irreducible` gives
\(f=f_1=f_2\), and injectivity of the transport gives equal minimal polynomials of \(c_1\) and
\(c_2\). `exists_unitFiltration_conj_of_minpoly_eq` then gives \(u\in U(\mathfrak A)\) with
\(u^{-1}b_1u-b_2\in\mathfrak P^{1-n}=\mathfrak P^{-(n-1)}\), which is membership in the coset of
the second stratum.

## Relation to the source

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), (1.4)–(1.5), printed
pp. 112–113 (PDF pp. 125–126), source `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`, with the layer
dimensions on printed p. 110 (PDF p. 123). The source obtains the factorization from BK93 (2.3)
and the formulas (1.5) from minimality, and refers the equal-factor implication to the first step
of the proof of BK93 (2.6.1), printed pp. 83–84 (PDF pp. 95–96), which uses the normal forms
(2.5.8) and (2.5.11), printed pp. 80–83. Source `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The Lean proof
follows this route with block matrices replaced by the successive quotients \(L_i/L_{i+1}\) and
the semisimple normal form replaced by `exists_linearEquiv_conj_of_aeval_irreducible`. A scalar
\(b\) is covered by the same argument, its minimality coming from
`LatticeChain.isMinimalOver_of_mem_range`.

## Imports

`MinimalSimpleStratumPolynomialStatement` (the target), `MinimalCriticalExponentProof`
(`minimalCriticalExponent`), `MinimalElementInvariants`, `PrincipalChainResidueDegree`,
`LatticeChainLayerIntertwining` and `SubfieldLayerLifting`
(`subfieldStabilizer_baseUniformizer`).
