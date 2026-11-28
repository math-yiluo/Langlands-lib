# Integral points of a congruence model after flat local base change

The proposition `CongruenceModelBaseChangeIntegralPointsStatement` identifies
the integral points of a positive-level congruence model after a flat local
extension of coefficients with the congruence subgroup of the extended model.
This file states the proposition and does not prove it.

## Setting

Let \(R\) be a discrete valuation ring with fraction field \(K\), and let \(A\)
be a local domain with fraction field \(L\). The coefficient square is the one
taken by `IntegralModel.baseChange`: algebra maps \(R\to A\to L\) and
\(R\to K\to L\) with both `IsScalarTower` instances, so the two composite maps
\(R\to L\) agree. The hypotheses on \(R\to A\) are

- `IsLocalHom (algebraMap R A)`: the map is local;
- `Module.Flat R A`: \(A\) is flat over \(R\);
- the explicit hypothesis
  `(IsLocalRing.maximalIdeal R).map (algebraMap R A) = IsLocalRing.maximalIdeal A`,
  that is, \(\mathfrak m_R A=\mathfrak m_A\).

The equality of ideals already implies that the map is local. The locality
instance is listed as well: it is the hypothesis under which
`congruenceKernelBaseChange` in
`Langlands.GroupScheme.IntegralModel.CongruenceBaseChange` restricts the
extension of integral sections to the congruence kernels.

The model `M : IntegralModel R K G` is an arbitrary integral model of the
\(K\)-group scheme \(G\): an affine, flat, locally finite-type group scheme over
\(R\) with its specified generic-fibre isomorphism. No smoothness, Henselian or
characteristic hypothesis is imposed. The irreducible element `ϖ` is the
uniformizer used by `congruenceModel`, and `n` is a positive natural number,
coerced to the natural-number index of `congruenceModel`.

## Assertion

Both sides are subgroups of `rationalPoints` of the base change of \(G\) along
`Spec.algebraMap K L`, the \(L\)-points of \(G_L\):

- the left side is `integralPoints` of
  `(M.congruenceModel hϖ n).baseChange A L`, the image of the \(A\)-sections of
  the pullback to \(A\) of the level-\(n\) congruence model \(M_n\), evaluated
  through its generic comparison `baseChangeGenericIso`;
- the right side is `(M.baseChange A L).congruenceSubgroupAt n`, the image in
  the same group of those \(A\)-sections of the pullback \(M_A\) of \(M\) whose
  restriction to \(A/\mathfrak m_A^n\) is the identity.

The statement asserts that the two subgroups are equal.

The maximal-ideal hypothesis is what makes the two levels agree. The
congruence model is defined by reduction modulo \(\mathfrak m_R^n\), and the
lifting criterion `congruenceModel_lift_iff` of
`Langlands.GroupScheme.Dilatation.CongruenceModel` describes the points of
\(M_n\) on a flat affine test scheme over \(R\) as the points of \(M\) whose
reduction along the quotient base is the identity. On the test ring \(A\) this
reduction is modulo \(\mathfrak m_R^n A\), whereas the congruence subgroup of
the extended model uses \(\mathfrak m_A^n\), and
\(\mathfrak m_R^n A=(\mathfrak m_R A)^n=\mathfrak m_A^n\). Without this
hypothesis the two reductions differ: if \(\mathfrak m_R A=\mathfrak m_A^e\),
as for a ramified extension of discrete valuation rings, Remark A.5.14 below
describes the \(A\)-points of \(M_n\) by reduction modulo \(\mathfrak m_A^{en}\).
That case is not part of the statement.

Over \(R\) itself, the module `Langlands.GroupScheme.Dilatation.CongruenceModel`
proves the analogous equality `integralPoints_congruenceModel`:
`(M.congruenceModel hϖ n).integralPoints = M.congruenceSubgroupAt n` for
positive `n`.

## Source

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition
A.5.12, Lemma A.5.13(3) and Remark A.5.14, printed pp. 636–637 (PDF
pp. 667–668). Definition A.5.12 writes \(\mathcal G(\mathfrak m^n)\) for the
kernel of \(\mathcal G(\mathfrak o)\to\mathcal G(\mathfrak o/\mathfrak m^n)\) and
defines the congruence group schemes \(\mathcal G_n\). Lemma A.5.13(3) states
\(\mathcal G_n(M_{\mathcal R}^m)=\mathcal G(M_{\mathcal R}^{m+n})\) inside
\(G(\mathcal R\otimes_{\mathfrak o}k)\) for every flat \(\mathfrak o\)-algebra
\(\mathcal R\), with \(M_{\mathcal R}=\mathfrak m\mathcal R\); extending the
notation of Definition A.5.12(1), \(\mathcal G(M_{\mathcal R}^j)\) is the kernel
of reduction \(\mathcal G(\mathcal R)\to\mathcal G(\mathcal R/M_{\mathcal R}^j)\),
so for \(m=0\) the left side is \(\mathcal G_n(\mathcal R)\). Remark A.5.14
describes \(\mathcal G_n\) as a single dilatation whose functor of points on
flat \(\mathfrak o\)-algebras is
\(\mathcal R\mapsto\ker(\mathcal G(\mathcal R)\to\mathcal G(\mathcal R/M_{\mathcal R}^n))\).

The statement is the case \(m=0\), \(\mathcal R=A\) of Lemma A.5.13(3), mapped
from \(G(A\otimes_R K)\) into \(G(L)\), with the reduction ideal rewritten by
\(\mathfrak m_R^n A=\mathfrak m_A^n\). Definition A.5.12 assumes an affine flat
group scheme of finite type, not a smooth one. Section A.5 reviews dilatations
over a Henselian discrete valuation ring, but the description of points on flat
test algebras behind Lemma A.5.13(3) and Remark A.5.14 (Proposition A.5.3,
printed p. 633, PDF p. 664) does not use Henselianity. Accordingly the
statement is over an arbitrary discrete valuation ring, as are
`congruenceModel` and `congruenceModel_lift_iff`.

- `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- `kaletha-prasad-2024-corrections`, version of 1 November 2024, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. Its
  Appendix A entry, printed p. 49, concerns only §A.4 (p. 604) and leaves
  Definition A.5.12, Lemma A.5.13 and Remark A.5.14 unchanged.
