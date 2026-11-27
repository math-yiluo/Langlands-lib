# Block data of a split fundamental stratum

This module constructs the splitting of a split fundamental stratum
\([\mathfrak A,n,n-1,b]\) together with the element \(\zeta\) of
Bushnell–Kutzko (8.2.9). It does so over any base ring \(O\) that is a
Henselian principal ideal local domain with fraction field \(K\). Among
these rings are \(\mathfrak o_F\) for a nonarchimedean local field
\(F\) and the integer ring of a finite extension of \(F\).

## Lattice-chain lemmas

For a lattice chain \(\mathcal L\) of period \(e\) and a prime element
\(\varpi\) (`RingPrimeElement`):

- `prime_smul_mem_lattice`, `prime_inv_smul_mem_lattice` and
  `prime_zpow_smul_mem_lattice` show that \(\varpi^k\) maps \(L_i\) into
  \(L_{i+ke}\) for \(k\in\mathbb Z\);
- `prime_zpow_smul_mem_endFiltration` gives the corresponding shift of
  the filtration;
- `pow_mem_endFiltration` gives \(x^k\in\mathfrak P^{km}\) for
  \(x\in\mathfrak P^m\).

They are the lemmas of `SplitObstructionIdempotents` for the integers
of a finite extension, stated here for a general base ring.

## Arithmetic and polynomial lemmas

- `exists_shift_exponents`: for coprime \(n\) and \(e>0\) there are
  \(t\ge 0\) and \(s\in\mathbb Z\) with \(tn-se=1\).
- `coeff_zero_ne_zero_of_irreducible`: a monic irreducible polynomial
  other than \(X\) has nonzero constant term.
- `exists_coprime_split_coeff`: let \(\varphi\) be monic, with distinct
  monic irreducible divisors \(p\ne X\) and \(q\). Then
  \(\varphi=gh\) with \(g,h\) monic, coprime and of positive degree, and
  \(g(0)\ne 0\). Here \(g\) is the largest power of \(p\) dividing
  \(\varphi\). This is the factorization of BK93, printed p. 276, with
  the factor \(f\) a power of one irreducible polynomial and
  \(f(0)\not\equiv 0\).

## The block data

`SplitBlockData D` for a stratum \(D=[\mathfrak A,n,r,b]\) records:

- elements \(e_1,e_2\) of \(\mathfrak A\) with \(e_1+e_2=1\),
  \(e_1e_2=0\), \(e_1\ne 0\), \(e_2\ne 0\), both commuting with \(b\);
- graded injectivity of \(x\mapsto bx-xb\) on both off-diagonal blocks.
  If \(x\in\mathfrak P^i\), \(e_1xe_2=x\) (respectively \(e_2xe_1=x\)) and
  \(bx-xb\in\mathfrak P^{i-n+1}\), then \(x\in\mathfrak P^{i+1}\);
- elements \(\zeta\in\mathfrak P\) and \(\zeta'\in\mathfrak P^{-1}\)
  commuting with \(b\), with \(\zeta\zeta'=\zeta'\zeta=e_1\) and
  \(e_1\zeta=\zeta e_1=\zeta\), \(e_1\zeta'=\zeta'e_1=\zeta'\).

`nonempty_splitBlockData` constructs such data for a stratum with
`Stratum.IsSplit`, \(b\in\mathfrak P^{-n}\), \(n>0\) and
\(\gcd(|n|,e)=1\). The proof follows that of
`exists_split_idempotents`.

1. The characteristic polynomial of \(y_b=\varpi^nb^e\) is the image of
   a monic \(\Phi\in O[X]\). Its reduction is `fundamentalPolynomial`.
2. The split hypothesis gives two distinct monic irreducible factors.
   One of them is different from \(X\), and `exists_coprime_split_coeff`
   factors the reduction with that factor's power first.
   `ValuationTheory.Henselian.exists_coprime_factor_lift` lifts the
   factorization to \(\Phi=f_1f_2\), where the reduction of \(f_1\) has
   nonzero constant term.
3. With \(uf_1+vf_2=1\), put \(e_1=(vf_2)(y_b)\) and \(e_2=(uf_1)(y_b)\).
   Cayley–Hamilton gives \(e_1e_2=0\). Polynomials in \(y_b\) over \(O\)
   lie in \(\mathfrak A\) and commute with \(b\), and the idempotents are
   nonzero by `not_isUnit_aeval_of_dvd_charpoly`.
4. Graded injectivity. If \(bx-xb\in\mathfrak P^{i-n+1}\), then
   \(y_bx-xy_b\in\mathfrak P^{i+1}\). The elements \(z\in\mathfrak A\) with
   \(zx-xz\in\mathfrak P^{i+1}\) form an \(O\)-subalgebra containing
   \(y_b\), hence \(e_2\). For \(x\) in an off-diagonal block,
   \(e_2x-xe_2=\pm x\).
5. The constant term \(a_0\) of \(f_1\) is a unit. Then
   \(W=-a_0^{-1}(f_1/X)(y_b)\,e_1\) satisfies \(y_bW=e_1\), so
   \(b_1'=\varpi^nb^{e-1}W\in\mathfrak P^{n}\) inverts \(b e_1\) on the
   first block.
6. With \(tn-se=1\), put \(\zeta=\varpi^{-s}b_1'^{\,t}e_1\) and
   \(\zeta'=\varpi^{s}(be_1)^te_1\). Their degrees are \(tn-se=1\) and
   \(-1\), and \(\zeta\zeta'=\zeta'\zeta=e_1\).

In the source, the element of (8.2.9) is \(\zeta_1=\varpi^q\,s(c)_{11}^t\)
with \(qe-tm=1\), extended by the identity on the second block. Here
\(\zeta\) is a power of the inverse of \(b\) on the first block, which
gives the same lattice properties (8.2.10). `SplitBlockData.shift`
in `DiagonalSplitTypeRefinement` adds \(e_2\) to obtain a unit.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (2.3.8)–(2.3.10), printed pp. 60–61,
(8.2.3), printed p. 276, and (8.2.9)–(8.2.10), printed pp. 278–279.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
