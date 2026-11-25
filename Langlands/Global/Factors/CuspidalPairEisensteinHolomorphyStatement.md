# Continuation and imaginary-axis holomorphy of the generic coefficient for a cuspidal pair

Module `Langlands.Global.Factors.CuspidalPairEisensteinHolomorphyStatement`
defines the proposition
`Langlands.Global.CuspidalPairEisensteinHolomorphyStatement.{u}`. It gives
no proof. The statement is the analytic input to the proof of Shahidi (1981),
Theorem 5.1, for \(G=\mathrm{GL}_N\), \(N=r+t+2\), with the upper block
parabolic \(P=MU_P\) of type \((r+1,t+1)\) and the inducing data
\(\pi\otimes(\pi')^\vee\) of Theorem 5.2. The sections `IsSection`, the
Eisenstein sum `eisensteinSeries`, the twist `heightPower` and the
coefficient `coeff` come from the namespace
`Langlands.Global.CuspidalPairEisenstein`. They are explained in
[CuspidalPairEisensteinSeries.md](CuspidalPairEisensteinSeries.md).

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`.
Let `T : CuspidalOperatorRealization F r` and
`T' : CuspidalOperatorRealization F t` be actual cuspidal realizations, both
with `HasUnitaryCentralCharacter`. Let `ψ` be an additive character of the
adeles with `IsStandardAdditiveCharacter F ψ`, and let `φ` satisfy
`IsSection T T' φ`. Then there is `Ec : ℂ → ℂ` such that:

1. `MeromorphicOn Ec Set.univ`. In Mathlib this means that at every point
   \(z_0\), some power \((z-z_0)^n\) times `Ec` is analytic at \(z_0\). The
   values of `Ec` at poles are not constrained.
2. `AnalyticAt ℂ Ec (y * Complex.I)` for every real \(y\). So `Ec` is
   holomorphic on a neighbourhood of every point of the line
   \(\operatorname{Re}s=0\), with its actual values there.
3. There is a real \(\sigma\) with `Ec s = coeff ψ φ s` whenever
   \(\operatorname{Re}s>\sigma\).

Here `coeff ψ φ s` is the actual integral
\(\int_{N_0(F)\backslash N_0(\mathbb A_F)}E(\phi,s,n)\overline{\psi_{N_0}(n)}\,dn\)
of the actual unconditional Eisenstein sum. Neither is a hypothesis. The
Lean sum is zero where its terms are not summable, and the Lean integral is
zero where the integrand is not integrable. The conclusion only uses `coeff`
on a right half-plane. In the source the series converges absolutely there
(see below), so condition 3 compares `Ec` with the true coefficient.
Together, conditions 1–3 say that the generic coefficient continues
meromorphically to \(\mathbb C\) and is holomorphic on the imaginary axis.
The continuation is unique where it is analytic, because \(\mathbb C\) is
connected and the poles of a meromorphic function are isolated.

The named arguments in `coeff (r := r) (t := t) ψ φ s` only fix the implicit
block sizes.

## Parameter and the imaginary axis

In a factorization \(g=u\operatorname{diag}(a,b)k\) the twist is

\[
  H(g)^s=|\det a|^{(t+1)s/N}\,|\det b|^{-(r+1)s/N}
        =\delta_P(\operatorname{diag}(a,b))^{s/N}
        =e^{\langle s\widetilde\alpha,\,H_P(g)\rangle},
  \qquad \widetilde\alpha=2\rho_P/N .
\]

The pairing of \(\rho_P\) with the coroot \(\alpha^\vee\) of the omitted
simple root is \(N/2\). So \(\widetilde\alpha=\langle\rho_P,\alpha^\vee\rangle^{-1}\rho_P\)
and \(\langle s\widetilde\alpha,\alpha^\vee\rangle=s\). Shahidi's
§5 parameter is \(-2z\rho_P\) in his sign convention, that is the twist
\(\delta_P^{z}\), with \(a_1=N\) in §2.3. It corresponds to
\(z=s/N\), so his line \(\operatorname{Re}z=0\) is the line
\(\operatorname{Re}s=0\) here. His region \(\operatorname{Re}z>1/2\) of
absolute convergence (p. 351) is \(\operatorname{Re}s>N/2\). It is the
region \(\operatorname{Re}\lambda-\rho_P\) in the positive chamber of
Mœglin–Waldspurger II.1.5 (pp. 85–86) for \(\lambda=s\widetilde\alpha\).

The sections are normalized: the slices carry the factor
\(\delta_P^{1/2}\) (`leviHalfCharacter`). The central characters of
\(\pi\) and \(\pi'\) are unitary, so \(\pi\otimes(\pi')^\vee\) is unitary.
Hence \(\operatorname{Re}s=0\) is the unitary axis.

## Source

Shahidi (1981), proof of Theorem 5.1, p. 352, writes the generic
coefficient as a product of local Whittaker values and the inverse of a
partial \(L\)-function (statement S1,
`CuspidalPairEisensteinCoefficientStatement`). It then concludes: by
compactness of \(U_{\mathbb A}/U_F\) the poles of the coefficient are among
those of the Eisenstein series \(E(s,\phi,e)\), and the theorem follows
from the holomorphy of \(E(it,\phi,e)\) for all real \(t\). The present
statement records both facts for the coefficient itself:

- meromorphic continuation of the Eisenstein series (Langlands; in the
  cuspidal case Mœglin–Waldspurger IV.1.8, p. 140; in general
  Bernstein–Lapid, Theorem 2.3 (1), journal p. 191);
- holomorphy on the unitary axis (Mœglin–Waldspurger IV.1.11 (b), p. 141;
  Lapid 2011, Proposition 6, p. 329);
- integration over the compact quotient \(N_0(F)\backslash N_0(\mathbb A_F)\),
  which carries both properties to the coefficient.

### Route through Mœglin–Waldspurger

Mœglin–Waldspurger IV treats the Eisenstein series of a cuspidal datum
\((M,\mathfrak P)\). Here \(\mathfrak P\) is the orbit of
\(\pi\otimes(\pi')^\vee\) under twisting by the characters
\(e^{\langle\lambda,H_M\rangle}\). The family
\(\phi_s=\phi\,e^{\langle s\widetilde\alpha,H_P\rangle}\) is a holomorphic
section over the line \(s\mapsto\pi_s\) in \(\mathfrak P\), and
\(E(\phi,s,g)=E(\phi_s,\pi_s)(g)\) in their notation. The steps are:

1. IV.1.11 (a): the singularities of \(E\) lie on a locally finite set of
   root hyperplanes \(\langle\pi,\alpha^\vee\rangle=c\). Along our line,
   \(\langle\pi_s,\alpha^\vee\rangle\) is \(s\) plus a constant. So each
   such hyperplane meets the line in at most one point, and the singular
   points on the line form a discrete set.
2. IV.1.9 (c) and (d): near \(\pi_{s_0}\), let \(d\) be a product of
   powers of the linear forms of the finitely many singular hyperplanes
   through \(\pi_{s_0}\), such that \(dE\) is holomorphic there. On the
   line, \(d(\pi_s)\) is a nonzero polynomial in \(s\). Then
   \((g,s)\mapsto d(\pi_s)E(\phi_s,\pi_s)(g)\) is smooth, and holomorphic
   in \(s\) for fixed \(g\).
3. On the compact quotient this function is jointly continuous. Integrating
   it against \(\overline{\psi_{N_0}}\) gives a holomorphic function of
   \(s\) near \(s_0\), by Morera's theorem and Fubini. So \(d(\pi_s)\) times the
   continued coefficient is holomorphic near \(s_0\). Hence the coefficient
   is meromorphic on \(\mathbb C\).
4. IV.1.11 (b): \(E\) is holomorphic at every \(\pi\) with
   \(\operatorname{Re}\pi=0\), that is at \(\pi_{iy}\). There one can take
   \(d=1\), and the coefficient is holomorphic at \(iy\).
5. For \(\operatorname{Re}s>N/2\) the series converges absolutely and
   locally uniformly (II.1.5). There the continuation is the sum, and the
   integral is the actual coefficient. Any \(\sigma\ge N/2\) works.

This route needs no restriction on the universe of `F`.

## Relation to the published general statements

This section explains how S2 follows from
`Langlands.Global.EisensteinMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicEisensteinContinuationStatement`, for `F : Type u`)
and `Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` (module
`Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement`, for
`F : Type`). Both are stated for a parabolic of a group scheme. Applying
them to \(\mathrm{GL}_N\) needs the following data:

- the group-scheme block parabolic `p : P ⟶ G`, `l : M ⟶ P`, its unipotent
  radical `iU`, and a `ParabolicRootPresentation p l a` for
  \(G=\mathrm{GL}_N\);
- `IsIwasawaCompact p K` for the transported standard compact subgroup. The
  matrix input is `exists_isStandardIwasawaFactorization`, and maximality is
  `PrimitiveAdelicHeight.isMaximalCompactSubgroup_generalLinear`, which
  transports `standardCompact F N` along
  `GeneralLinearGroupPoints.adelicHomeomorph`;
- the identification of `heightPower F r t s` with the Library power of the
  parameter \(s\widetilde\alpha\), so that `eisensteinSeries` becomes
  `hK.eisensteinSeries` after transport along
  `GeneralLinearGroupPoints.adelicEquiv`.

Given this data, the derivation runs as follows. This is an explanation, not
a Lean proof.

1. **The section is an automorphic form on \(U_P(\mathbb A)M(F)\backslash G(\mathbb A)\).**
   `IsSection` gives left \(U_P(\mathbb A)\)-invariance, archimedean
   smoothness, right invariance under an open subgroup of the finite adelic
   group, and finite-dimensional span of the right
   \(K\)-translates. Left \(M(F)\)-invariance holds because the slices are
   spanned by products of cusp forms, and \(\delta_P\) is trivial on
   \(M(F)\) by the product formula. Cusp forms are \(\mathfrak Z\)-finite and
   bounded, so the section is \(\mathfrak Z\)-finite and of moderate growth.
   These are the conditions of `IsAutomorphicFunctionOn` for
   `parabolicQuotientSubgroup`.
2. **Removing the unitary exponent.** The central characters of \(\pi\)
   and \((\pi')^\vee\) are unitary. Their restriction to the split component
   \(A_M\) can still be nontrivial, of the form
   \(e^{\langle i\mu,H_M\rangle}\) with \(\mu\in\mathfrak a_P^*\) real. Then
   \(\phi_0=e^{-\langle i\mu,H_P\rangle}\phi\) satisfies Lapid's condition
   \(\phi_0(ag)=\delta_P(a)^{1/2}\phi_0(g)\) for \(a\in A_M\) (§2, p. 311;
   `IsSplitComponentEquivariant`). Its normalized slices are spanned by
   products of cusp forms times the unitary character
   \(e^{-\langle i\mu,H_M\rangle}\). These are \(A_M\)-invariant and square
   integrable on \(A_MM(F)\backslash M(\mathbb A)\), since cusp forms are
   rapidly decreasing modulo the centre. The slice at \(k\) is the slice at
   the identity of the right translate by \(k\). By \(K\)-finiteness the
   slices lie in one finite-dimensional space, and they depend continuously
   on \(k\). So
   \(\int_K\int_{A_MM(F)\backslash M(\mathbb A)}\delta_P^{-1}|\phi_0(mk)|^2<\infty\).
   So \(\phi_0\in A^2_P\) (`IsSquareIntegrableInducedForm`), and
   \(E(\phi,s,g)=E(\phi_0,\lambda(s),g)\) with
   \(\lambda(s)=i\mu+s\widetilde\alpha\). For \(s=iy\) the parameter
   \(\lambda(iy)\) lies in \(i\mathfrak a_P^*\).
3. **Continuation of the coefficient.**
   `EisensteinMeromorphicContinuationStatement` gives, near each parameter,
   a meromorphic function \(f\) with values in one Fréchet space
   \(\mathfrak F^R_L\) of functions of uniform moderate growth. Its value is
   \(E'(\lambda)\) on the holomorphy domain, and \(E'\) is the Eisenstein
   series for sufficiently regular \(\operatorname{Re}\lambda\). The
   coefficient functional \(\ell(h)=\int h(n)\overline{\psi_{N_0}(n)}\,dn\)
   is continuous on \(\mathfrak F^R_L\): on a compact set of
   representatives of the quotient, the growth weight is bounded, so the
   zeroth growth seminorm controls the supremum. So \(\ell\circ f\) is a
   scalar meromorphic function. Choose linear coordinates in which
   \(\lambda(s)\) is a coordinate line. In a local quotient
   \(g\cdot f=h\), divide \(g\) and \(h\) by the largest power of the
   equation of that line dividing \(g\). The restricted quotient
   \(\ell(h)/g\) is then a meromorphic function of \(s\). Two local quotients
   agree as meromorphic germs on overlaps, because the holomorphy domain is
   dense. For \(\operatorname{Re}s\) large, \(\lambda(s)\) is regular and the
   quotient equals the absolutely convergent coefficient. This gives `Ec`
   and \(\sigma\).
4. **Holomorphy on the axis.** `EisensteinImaginaryAxisHolomorphyStatement`
   applied to \(\phi_0\) and to the continuation \(E'\) of step 3, evaluated
   pointwise, gives, for each \(g\), a function
   \(\lambda\mapsto E''(\lambda,g)\) holomorphic near \(\lambda(iy)\) that
   agrees with \(E'(\lambda,g)\) on a dense open set. Evaluation at \(g\) is
   continuous on \(\mathfrak F^R_L\). So \(g\cdot E''(\cdot,g)\) equals the
   evaluation of \(h\) near \(\lambda(iy)\). Restrict to the line. If \(g\)
   vanishes to order \(m\) at \(s=iy\), then every evaluation of the
   Fréchet Taylor coefficients of \(h\) of order below \(m\) vanishes.
   Evaluations separate the elements of \(\mathfrak F^R_L\), so those
   coefficients are zero. Hence \(\ell(h)/g\) is holomorphic at \(iy\).
   This holomorphy does not follow from the pointwise statement alone: the
   Fréchet continuation is needed to pass from evaluations to the
   integral.
5. **Universe.** The imaginary-axis statement quantifies only over
   `F : Type`. A number field `F : Type u` is isomorphic to a number field
   `F₀ : Type` (for example `ℚ[X]/(f)` for a primitive element). Transport
   the sections, cusp forms, the character `ψ` and the coefficient along
   the induced adelic isomorphism `AdelicGLTransport.adelicEquiv`. The
   coefficient does not
   change, because the normalized Haar measure on the compact quotient is
   preserved. So S2 for `F` follows from the case of `F₀`.

## Use

`Langlands.Global.cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein`
(module `Langlands.Global.Factors.CuspidalPairEisensteinDerivation`), on the
way to `CuspidalPairBoundaryNonvanishingStatement`, combines S2 with S1
(`CuspidalPairEisensteinCoefficientStatement`).
At a point \(s_0\) of the imaginary axis, S1 gives a section and a
numerator \(c\), nonzero at \(s_0\), with
\(c(s)=L^{S_0}(1+s,\pi\times\pi')\cdot\mathrm{coeff}(\psi,\phi,s)\) on a
right half-plane. S2 for the same section makes the coefficient holomorphic
at \(s_0\). By uniqueness of continuation, \(L^{S_0}(1+s)\) continued has
no zero at \(s_0\). This is the non-vanishing argument of Shahidi (1981),
p. 352.

## References

- F. Shahidi, *On Certain L-Functions*, Amer. J. Math. 103 (1981),
  297–355: Theorem 5.1 and its proof, pp. 351–352.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
  Series*, Cambridge University Press, 1995: II.1.5, pp. 85–86 (chapter
  file `06.1_pp_78_100_Definitions.pdf`); IV.1.8, IV.1.9 (c)–(d), IV.1.11
  (a)–(b), pp. 140–141 (chapter file `08.1_pp_135_141_The_results.pdf`).
- J. Bernstein and E. Lapid, *On the meromorphic continuation of
  Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234: Theorem 2.3
  (1) and (6), p. 191.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13
  (2011), 309–331: §2, p. 311 (\(A^n_P\), \(A^2_P\)); Proposition 6, p. 329.
