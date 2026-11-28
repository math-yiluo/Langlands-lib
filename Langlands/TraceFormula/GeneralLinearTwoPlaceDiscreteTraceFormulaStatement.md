# The simple discrete trace formula at two finite places for `GL_n`

`Langlands.TraceFormula.GeneralLinearTwoPlaceDiscreteTraceFormulaStatement`
is a proposition definition. Let \(F\) be a number field and
\(G=\mathrm{GL}_n\) with \(n>0\) and connected reductivity witness `hG`.
The function \(f\) satisfies `IsAdelicTestFunction`, and every point of
its closed support has regular elliptic components at the two distinct
finite places \(p_1,p_2\). Assume `hf : Integrable f Measure.haar` and
that `T = canonicalDiscreteIntegratedAction F G hG f hf` on the
full discrete spectrum is trace class.

Write \(H=G(\mathbb A_F)^1\), let \(\Gamma\leq H\) be the rational image,
and let \(f^1\) be `canonicalNormOneAverage F G hG f`.
There is a finite family of regular elliptic rational points \(r_j\).
Their images \(q_j\) in \(\Gamma\) are pairwise nonconjugate under
\(\Gamma\). If the orbit function \(x\mapsto f^1(x^{-1}\delta x)\) for
\(\delta\in\Gamma\) takes a nonzero value on \(H\), then \(\delta\) is
\(\Gamma\)-conjugate to some \(q_j\).

With \(C_j=Z_H(q_j)\), `SimpleTraceGeometricExpansion` for the identity
twist gives

\[
\operatorname{tr}(T)=
\sum_j \operatorname{vol}((\Gamma\cap C_j)\backslash C_j)
    \int_{C_j\backslash H} f^1(x^{-1}q_jx)\,dx.
\]

For every compatible family of centralizer and quotient measures the
covolumes are finite and the orbit functions are integrable. The
ambient Haar measure is `Measure.haar` on \(H\) and the rational
centralizers have counting measure.

## Source and normalization

Arthur's *The invariant trace formula II. Global theory*, Corollary 7.5
(printed p. 541, PDF p. 41), equates the sum of elliptic orbital terms
for \(\mathrm{GL}_n\) with the sum of discrete traces indexed by \(t\).
On pp. 538–539 (PDF pp. 38–39), Arthur's local cuspidality condition for a
product test \(h\) is \(h_{v,M}=0\) for every proper Levi \(M\). A
sufficient condition is vanishing of orbital integrals at every regular
nonelliptic element. The conjugacy classes of these elements are
disjoint from regular elliptic support.
The registered source is `arthur-1988-invariant-trace-formula-II`,
SHA-256 `42d2193dde29d159ebf757e3636f7ab3e4c0c85644cac360baffb7e0758e507b`.

Arthur's distributions factor through restriction to \(H\) (printed
p. 504, PDF p. 4). In this formulation multiplication gives
\(G(\mathbb A_F)=A_G\times H\), where \(A_G\) is the positive split
center at infinity. The action on \(A_G G(F)\backslash G(\mathbb A_F)\)
is trivial on \(A_G\). The product Haar convention in
`canonicalNormOneAverage` gives \(R(f)=R(f^1)\) under the norm-one
quotient identification by integrating first along \(A_G\). Also
\(G(\mathbb A_F,r_j)=A_G\times C_j\), so Arthur's orbital quotient
and rational centralizer quotient give the two quotients in the
displayed formula. For a fixed Haar measure on \(H\), scaling the
centralizer Haar measure scales the covolume and orbital integral
reciprocally, as in `orbitalTerm_eq_of_isCompatible`.

## Passage to smooth adelic tests

The average \(f^1\) is smooth at infinity and supported in the compact
image of `tsupport f` under projection to \(H\). Since \(A_G\) has
trivial finite components, the projection preserves the two
finite-place conditions. Extend \(f^1\) to a compactly supported test
\(h(a x)=\psi(a)f^1(x)\) with \(\psi\in C_c^\infty(A_G)\) and
\(\psi(1)=1\). With a fixed compact open product level in the finite
adeles, \(h\) is a finite sum of archimedean functions times indicators
of finite-adelic cosets. Each nonzero summand has regular elliptic
support at both places.

Let \(K_\infty\subset H\) be the archimedean maximal compact subgroup.
Convolving \(h\) on each side by the sum of the character idempotents
for an increasing finite set of \(K_\infty\)-types gives \(h_N\).
Its finite factors are preserved by these convolutions. The
restrictions \(f_N=h_N|_H\) are supported in the fixed compact set
\(D=K_\infty\,\operatorname{tsupp}(f^1)\,K_\infty\) and converge
uniformly to \(f^1\). Smooth Peter–Weyl convergence is uniform here
because the derivatives in \(K_\infty\times K_\infty\) of the
left and right translates are bounded uniformly on the compact
support at the fixed finite level.

At fixed \(N\), the product formulation of Corollary 7.5 applies by
linearity and density. Approximate each joint archimedean factor of
\(h_N\) by finite sums of products over the infinite places in the
smooth topology with fixed compact support. Applying the same
compact-type projections preserves this approximation and the finite
factors. The discrete integrated action on the resulting Fréchet space
with fixed compact support, finite level and finite types is continuous
into the trace class.
Indeed, Müller's compact-type trace-class theorem, as stated in
Getz–Hahn, *An Introduction to Automorphic Representations*, Theorem
9.1.4 (printed p. 242, PDF p. 254), gives trace class for these tests
after restriction to \(H\). The \(L^1\) bound gives continuity in
operator norm, so the closed graph theorem gives continuity in trace
norm. The orbital integrals pass through this approximation by the
compact-support argument below. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

On the geometric side every rational orbit meeting \(D\) is regular
elliptic at both finite places, hence its rational characteristic
polynomial is irreducible and separable. The coefficients of the
characteristic polynomials on \(D\) lie in a compact subset of
\(\mathbb A_F^n\). Its intersection with the closed discrete
diagonal \(F^n\) is finite, and each such polynomial determines a
single rational conjugacy class. The same argument applies to the
fixed supports of the product approximants. For each class the
centralizer quotient maps homeomorphically onto the closed orbit,
so all orbit functions in the approximation are supported in a
single compact subset of that quotient. Uniform convergence then
gives convergence of orbital integrals for the compatible regular
measures. The theorem `generalLinearEllipticCentralizer` supplies
the finite covolumes and integrable orbit functions for these classes.

On the spectral side \(R_{\mathrm{disc}}(f_N)=P_N T P_N\), where
\(P_N\) is the orthogonal projection onto the chosen isotypic
subspaces of the discrete spectrum. The summands of Arthur's
discrete spectrum indexed by \(t\) are orthogonal invariant summands,
so the sum of their traces is the full trace. As \(P_N\) converges
strongly to the identity and \(T\) is trace class, \(P_N T P_N\)
converges to \(T\) in trace norm. Thus the finite geometric sum for
the approximants tends to the sum for \(f^1\) and the corresponding
traces tend to \(\operatorname{tr}(T)\).
