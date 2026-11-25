# Joint continuation of the cuspidal-pair Eisenstein series

Module `Langlands.Global.Factors.CuspidalPairEisensteinJointContinuationStatement`
defines the proposition
`Langlands.Global.CuspidalPairEisensteinJointContinuationStatement.{u}`. It gives
no proof. It is the Eisenstein-series input of
[`CuspidalPairEisensteinHolomorphyStatement`](CuspidalPairEisensteinHolomorphyStatement.md)
(statement S2 of the Shahidi route), with the integration over the compact
unipotent quotient removed. That integration is the separate step
[`CuspidalPairEisensteinHolomorphyReduction`](CuspidalPairEisensteinHolomorphyReduction.md).

The group is \(G=\mathrm{GL}_N\), \(N=r+t+2\), with the upper block parabolic
\(P=MU_P\) of type \((r+1,t+1)\). The sections `IsSection`, the Eisenstein sum
`eisensteinSeries` and its twist \(H(g)^s=\delta_P(g)^{s/N}\) are those of
[`CuspidalPairEisensteinSeries`](CuspidalPairEisensteinSeries.md).

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`. Let
`T : CuspidalOperatorRealization F r` and `T' : CuspidalOperatorRealization F t`
both have `HasUnitaryCentralCharacter`, and let `φ` satisfy `IsSection T T' φ`.
Then there are a function `E : ℂ → AdelicGL F N → ℂ` and a real `σ` such that:

1. `E s = eisensteinSeries F φ s` (as functions on \(\mathrm{GL}_N(\mathbb A_F)\))
   whenever \(\sigma<\operatorname{Re}s\).
2. For every \(s_0\in\mathbb C\) there are `m : ℕ`, a set `W` and
   `h : ℂ → AdelicGL F N → ℂ` such that
   - `W` is open and contains \(s_0\);
   - \((s,g)\mapsto h(s,g)\) is continuous on \(W\times\mathrm{GL}_N(\mathbb A_F)\)
     (product topology);
   - \(s\mapsto h(s,g)\) is complex differentiable on \(W\) for every \(g\);
   - \(h(s,\gamma g)=h(s,g)\) for \(s\in W\), \(\gamma\in\mathrm{GL}_N(F)\)
     (`AdelicGL.rational`) and every \(g\);
   - \(h(s,g)=(s-s_0)^m\,E(s,g)\) for \(s\in W\), \(s\ne s_0\) and every \(g\);
   - if \(\operatorname{Re}s_0=0\), then \(m=0\) and also \(h(s_0,\cdot)=E(s_0,\cdot)\).

No additive character occurs. The Lean sum `eisensteinSeries` is zero where its
terms are not summable; clause 1 is only about the half-plane, where the series
converges absolutely (below). At a pole \(s_0\) the value \(E(s_0,\cdot)\) is not
constrained. At points of the imaginary axis the last clause says that \(E\)
itself is jointly continuous and holomorphic in \(s\) near \(s_0\), with its
actual values.

Clause 2 makes \(s\mapsto E(s,g)\) meromorphic on \(\mathbb C\) for every \(g\),
with poles of order at most \(m\) at \(s_0\) and the same denominator for all
\(g\). Clause 1 identifies \(E\) with the Eisenstein series on a right
half-plane. So \(E\) is the meromorphic continuation of the Eisenstein series in
\(s\), with a single local denominator for all \(g\), and it is holomorphic on
the line \(\operatorname{Re}s=0\).

## Source

The statement specializes Mœglin–Waldspurger, Chapter IV, to the line of
parameters of Shahidi (1981), §5. It is a derived statement.

**The cuspidal datum and the line.** \(M=\mathrm{GL}_{r+1}\times\mathrm{GL}_{t+1}\)
is the standard block-diagonal Levi. Let \(\pi_0=\pi\otimes(\pi')^\vee\), where
\(\pi\) and \((\pi')^\vee\) are the irreducible cuspidal representations
realized by `T` and `dualRealization T'` (`CuspidalOperatorRealization` contains
irreducibility). Let \(\mathfrak P\) be the orbit of \(\pi_0\) under twisting by
the unramified characters of \(M\) trivial on the centre of \(G\). Then
\((M,\mathfrak P)\) is a cuspidal datum in the sense of MW IV.1.2. `IsSection`
says that \(\phi\) is right \(K\)-finite and that its normalized slices
\(m\mapsto\delta_P(m)^{-1/2}\phi(mk)\) lie in the space of \(\pi_0\). In the
notation of MW II.1.1 and I.2.17 this is \(\phi\in A(U(\mathbb A)M(k)\backslash G)_{\pi_0}\)
(the factor \(m^{\rho_P}=\delta_P(m)^{1/2}\)). Put
\(\widetilde\alpha=2\rho_P/N\) and \(\pi_s=\pi_0\otimes e^{\langle s\widetilde\alpha,H_M(\cdot)\rangle}\).
The function \(s\mapsto\phi\,H^s\) is the canonical holomorphic section
\(\pi_s\mapsto\lambda\phi\) of MW IV.1.3, restricted to the line, and
\(E(\phi,s,g)=E(\phi H^s,\pi_s)(g)\) in MW's notation, where the series converges.

**Clause 1.** MW II.1.5, Proposition (pp. 85–86): for cuspidal data the series
converges normally for \(g\) in compact sets and parameters near \(\pi\) whenever
\(\langle\operatorname{Re}\pi,a\rangle>\langle\rho_P,a\rangle\) for the simple root
\(a\) of \(A_M\) in \(U_P\). Since the central characters of \(T\) and \(T'\) are
unitary, \(\operatorname{Re}\pi_0=0\) and \(\operatorname{Re}\pi_s=(\operatorname{Re}s)\widetilde\alpha\).
With \(\langle\widetilde\alpha,a^\vee\rangle=1\) and \(\langle\rho_P,a^\vee\rangle=N/2\)
(see [`CuspidalPairEisensteinHolomorphyStatement.md`](CuspidalPairEisensteinHolomorphyStatement.md)),
the region is \(\operatorname{Re}s>N/2\). Normal convergence makes the sum
absolutely summable, so it equals the Lean `tsum` there, and by MW IV.1.7 the
continuation below agrees with it on this region. Any \(\sigma\ge N/2\) works.

**Clause 2.** MW IV.1.8 (a) (p. 140) continues \(E\) meromorphically to
\(\mathfrak P\). MW IV.1.11 (a) (p. 141) puts its singularities on a locally
finite set of root hyperplanes. For a number field these are
\(\{\pi_0\otimes\lambda:\langle\lambda,a^\vee\rangle=c\}\) (MW IV.1.6 (i)), and
\(a\) is the only indivisible root of \(A_M\) in \(U_P\) because \(P\) is
maximal. On the line, \(\langle s\widetilde\alpha,a^\vee\rangle=s\), so each
hyperplane meets the line in one point and the singular parameters form a
discrete subset of \(\mathbb C\). Near \(s_0\), the product \(d\) of the powers of
the forms of the hyperplanes through \(\pi_{s_0}\) given by IV.1.11 (a) is
\((s-s_0)^m\) on the line, up to a factor that does not vanish near \(s_0\). By
MW IV.1.9 (d) together with (c) (i)–(ii) (p. 140),
\((g,\pi)\mapsto d(\pi)E(\phi(\pi),\pi)(g)\) is smooth on \(G\times V\) and
holomorphic in \(\pi\). Dividing by that nonvanishing factor and restricting to
the line gives \(h\). Choose \(W\) so small that it contains no other singular
parameter. By MW IV.1.9 (b) (i), \(E(\phi(\pi),\pi)\) is an automorphic form on
\(G(k)\backslash G\) at regular \(\pi\), so \(h(s,\cdot)\) is left
\(\mathrm{GL}_N(F)\)-invariant for \(s\ne s_0\) and, by continuity, at \(s_0\).
Off the poles, \(E(s,\cdot)\) is defined as the continued Eisenstein series.

**The imaginary axis.** If \(\operatorname{Re}s_0=0\), then
\(\operatorname{Re}\pi_{s_0}=0\), and MW IV.1.11 (b) (p. 141) says that \(E\) is
holomorphic at \(\pi_{s_0}\). Then no hyperplane is needed, \(m=0\), and
\(h=E\) near \(s_0\) by IV.1.9 (c) (i).

Bernstein–Lapid, Theorem 2.3 (1) and (6) (journal p. 191), with the Fréchet
form of the Corollary in §8.6, and Lapid (2011), Proposition 6 (p. 329), give
the same facts for general inducing data. The Library states them as
`EisensteinMeromorphicContinuationStatement`,
`EisensteinJointRootHyperplaneStatement` and
`EisensteinImaginaryAxisHolomorphyStatement`. Deriving the present statement from
them also needs the comparison of the two-block parabolic of
\(\mathrm{GL}_N\) with the group-scheme formalism (presentation, Iwasawa
compact, heights and sections), described in
[`CuspidalPairEisensteinHolomorphyStatement.md`](CuspidalPairEisensteinHolomorphyStatement.md).
No proof of the present statement, from either route, is in the Library.

## References

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
  Series*, Cambridge University Press, 1995: II.1.1 and II.1.5, pp. 78–79 and
  85–86 (chapter file `06.1_pp_78_100_Definitions.pdf`); IV.1.2, IV.1.3, IV.1.6,
  IV.1.7, IV.1.8, IV.1.9 (b)–(d), IV.1.11 (a)–(b), pp. 136–141 (chapter file
  `08.1_pp_135_141_The_results.pdf`).
- F. Shahidi, *On Certain L-Functions*, Amer. J. Math. 103 (1981), 297–355:
  §5, proof of Theorem 5.1, pp. 351–352.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), 187–234: Theorem 2.3 (1) and (6),
  p. 191.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), 309–331: Proposition 6,
  p. 329.
