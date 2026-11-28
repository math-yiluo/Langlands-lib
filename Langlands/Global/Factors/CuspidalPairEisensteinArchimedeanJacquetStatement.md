# The archimedean Jacquet integral for a pair of cuspidal Whittaker spaces

The module states `Langlands.Global.CuspidalPairEisensteinArchimedeanJacquetStatement.{u}`.
Set \(N=r+t+2\), and let \(P=MU\) be the standard upper block parabolic of
\(\mathrm{GL}_N\) with block sizes \(r+1,t+1\). Use the standard maximal compact subgroup
\(K_\infty\) in \(\mathrm{GL}_N(F_\infty)\).

## Inducing spaces and sections

For a cuspidal realization \(T\) and a finite set \(S\) of finite places,
`sphericalSubmodule T S` consists of the cusp vectors fixed by the local integral
subgroups at every finite place outside \(S\). `whittakerSpace T ψ hψ S` is its image
under `ArchimedeanWhittakerEvaluation.coefficient T ψ hψ 1`. These are smooth functions
on the archimedean group, obtained by evaluating the global Whittaker coefficient at
finite component \(1\). The two inducing spaces \(W,W'\) use \(T\) and `dualRealization T'`,
respectively. `leviWhittakerSpace W W'` is the complex span of the functions
\((m_1,m_2)\mapsto W_1(m_1) W_2(m_2)\) with \(W_1\in W\) and \(W_2\in W'\).

`IsInducedSection` describes the scalar Whittaker realization of smooth \(K_\infty\)-finite
normalized induction. A smooth scalar function \(f\) on \(\mathrm{GL}_N(F_\infty)\) is
left \(U(F_\infty)\)-invariant. For every \(k\in K_\infty\),
`infiniteNormalizedSlice f k`, the function \(m\mapsto\delta_P(m)^{-1/2}f(mk)\),
belongs to `leviWhittakerSpace W W'`. The right \(K_\infty\)-translates of \(f\) span a
finite-dimensional space. The existential quantifier on \(f\) ranges over all sections
satisfying these conditions. In the compact picture, a vector-valued induced section
\(\Phi\) in the smooth Levi Whittaker model gives \(f(g)=\Phi(g)(1)\). By normalized
Levi covariance, the slice at \(k\) then recovers \(\Phi(k)\) as a function on the Levi.

## Integrand and statement

At \(X\in M_{(t+1)\times(r+1)}(F_\infty)\), `jacquetIntegrand ψ f s` is \(f\) at the
archimedean projection of \(w u'(X,0)\), times `heightPower` at that same archimedean
point with finite component \(1\), times the conjugate of the standard additive
character on \(u'(X,0)\). The block Weyl representative \(w\), exchanged radical
\(u'\), height, phase and measure are those of the
[archimedean open-cell integral](CuspidalPairEisensteinArchimedeanNumeratorStatement.md).
For a parabolic Iwasawa factorization \((g,1)=pk\) of the argument of `heightPower`,
the height factor is \(\exp((s/N)\log\delta_P(p))\).

For a number field \(F:\mathrm{Type}\,u\) with compact `AdeleQuotient F`, actual
cuspidal realizations \(T,T'\) with unitary central characters, a standard additive
character \(\psi\) and a finite \(S\) for which both \(W\) and \(W'\) are nonzero,
the proposition asks for such a section \(f\) at every \(s_0\) with \(\operatorname{Re}s_0=0\).
There must be a meromorphic function \(c\) on \(\mathbb C\), analytic and nonzero
at \(s_0\), and a real \(\sigma\) such that the Jacquet integrand is integrable
for \(\operatorname{Re}s>\sigma\) and its Haar integral equals \(c(s)\) there.

## Provenance

This is a derived product-of-archimedean-places formulation of the local
Jacquet-integral step in Shahidi, *On certain L-functions*, Amer. J. Math. 103
(1981), proof of Theorem 5.1, pp. 351–352 (PDF pp. 56–57). Page 352 uses absolute
convergence of the archimedean component on a right half-plane and a choice of
local vector with nonzero Whittaker value at the parameter in question. Proposition
3.2, p. 333 (PDF p. 38), gives entire continuation and nondegeneracy for fine
inducing representations. The \(\mathrm{GL}_{n+m}\) example following Theorem 4.1,
p. 344 (PDF p. 49), invokes fineness for the unitary cuspidal components. The single
parameter and Haar integral here combine the archimedean places of the number field.
For a tensor of local test sections, absolute convergence gives the product of the
local integrals on a common right half-plane. Changing from product Haar measure
to `archimedeanOpenCellHaar` multiplies this product by a positive constant.
The conclusion retains meromorphy and regular nonvanishing at the prescribed point.

Shahidi, *Whittaker models for real groups*, Duke Math. J. 47 (1980), p. 120
(PDF p. 22), requires that each infinitesimal principal-series embedding extend
to a bicontinuous isomorphism onto the corresponding smooth subrepresentation.
The remark on that page records fineness for irreducible unitary representations
of real and complex general linear groups. Equation (3.1) matches the inducing
Whittaker functional with the restriction of the principal-series functional.
Proposition 3.2 and its proof, pp. 120–121 (PDF pp. 22–23), use the fine smooth
inducing representation and induction in stages to obtain nondegeneracy.
Lemma 3.1, p. 121 (PDF p. 23), matches the induced Levi intertwiner with the
principal-series intertwiner. Corollary 3.2, on the same page, obtains the induced
Whittaker functional by composing the principal-series Jacquet functional with
the induced embedding.

## Comparison with the actual Whittaker spaces

Write \(W_x^\psi(g_\infty,g_f)\) for the global Whittaker coefficient of a
cuspidal vector \(x\). The functional on the actual cuspidal carrier is
\(\lambda_T(x)=W_x^\psi(1,1)\). In a tensor comparison \(e\) with the actual
carrier, fix a finite vector \(b\) spherical outside \(S\). On the archimedean
factor the functional is \(a\mapsto\lambda_T(e(a\otimes b))\), with \(a\) a
compact-finite vector. The comparison with Shahidi's inducing data must identify
the actual function \(g_\infty\mapsto W_{e(a\otimes b)}^\psi(g_\infty,1)\) with
the coefficient of this functional applied to the translate of \(a\) in the
fine smooth globalization. A nonzero compatible functional agrees up to a
nonzero scalar with the product of the local Whittaker functionals for
\(\psi_\infty\). This scalar is independent of \(s\) and preserves the conclusion
about nonvanishing. The same comparison uses `dualRealization T'` for the second
block.

The comparison uses the compact and Lie actions, compact and center finiteness,
moderate growth, and the standard unipotent transformation law. The coefficient
map transports the compact and Lie actions and joint finiteness through
`coefficient_compact`, `coefficient_lie`, and `coefficient_jointFinite`.
[Archimedean Whittaker evaluation](../RankinSelberg/ArchimedeanWhittakerIdentityEvaluation.md)

Registered sources

- `shahidi-1981-certain-l`, SHA-256 `66e7148a9c31eaf9318e7936141ae6083587fbf15e3e239af244826572483ea4`.
- `shahidi-1980-whittaker-real`, SHA-256 `dc8a3472b35e33290db480a7f8b9d32b42981fd19c36a79f179607979a2417af`.
