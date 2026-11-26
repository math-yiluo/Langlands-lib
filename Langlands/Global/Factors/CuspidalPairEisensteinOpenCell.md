# The open-cell integral of a cuspidal-pair Eisenstein series

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCell` defines the
integral over the open Bruhat cell to which the generic Fourier coefficient
`CuspidalPairEisenstein.coeff` of the Eisenstein series
`CuspidalPairEisenstein.eisensteinSeries` unfolds. The series, its sections
and the coefficient are those of
[CuspidalPairEisensteinSeries.md](CuspidalPairEisensteinSeries.md). All
declarations are in the namespace `Langlands.Global.CuspidalPairEisenstein`.

## Setting

Let \(N = r+t+2\), \(G = \mathrm{GL}_N\), and let \(P = MU\) be the upper
parabolic `blockShape r t` with ordered blocks of sizes \(a = r+1\) and
\(b = t+1\), so \(M = \mathrm{GL}_a \times \mathrm{GL}_b\). Let \(N_0\) be the
upper unitriangular subgroup of \(G\), \(N_M = N_0 \cap M\), and
\(\psi_N(n) = \psi(n_{0,1} + \dots + n_{N-2,N-1})\) the generic character of
\(N_0(\mathbb A)\) used in `coeff` (`genericCharacter` with all coefficients
\(1\)).

## Definitions

- `leviPair F r t x y` is the block-diagonal matrix \(\mathrm{diag}(x, y)\)
  for \(x \in \mathrm{GL}_a(\mathbb A)\), \(y \in \mathrm{GL}_b(\mathbb A)\):
  the Library Levi embedding `(blockShape r t).leviEmbedding` applied to the
  pair through `Shahidi.twoBlockLeviEquiv`.
- `leviWhittaker F r t ψ f g` is the generic Whittaker coefficient of
  \(f\) along \(N_M\) at \(g\),
  \[
    W_M(f)(g) = \int_{N_a(F)\backslash N_a(\mathbb A)}
      \int_{N_b(F)\backslash N_b(\mathbb A)}
      f(\mathrm{diag}(u_1,u_2)\,g)\,
      \overline{\psi_a(u_1)}\,\overline{\psi_b(u_2)}\,du_2\,du_1 ,
  \]
  written as two nested applications of the Library's global Whittaker
  coefficient `generalLinearWhittakerFunction` (Getz–Hahn (11.6)) on
  \(\mathrm{GL}_a\) and \(\mathrm{GL}_b\), with their generic characters
  \(\psi_a, \psi_b\) (all coefficients \(1\)) and quotient measures of total
  mass one. The character \(\psi_N\) restricts on \(N_M\) to
  \(\psi_a \otimes \psi_b\). As for every Library Bochner integral, an
  integral of a non-integrable function is \(0\).
- `openCellWeyl F r t` is Shahidi's block Weyl representative
  \(w = \begin{pmatrix} 0 & I_a \\ I_b & 0 \end{pmatrix}\)
  (`Shahidi.blockWeyl (r+1) (t+1)`), and `openCellUnipotent F r t Y` is
  \(u'(Y) = \begin{pmatrix} I_b & Y \\ 0 & I_a \end{pmatrix}\)
  (`Shahidi.intertwiningUnipotent (r+1) (t+1)`) for an adelic
  \(b \times a\) matrix \(Y\). They are the coordinates of Shahidi (1984),
  printed page 72, (0.2), used by the local module
  `Langlands.Representation.Shahidi.JacquetIntegral`; here they are taken over
  the adele ring and reindexed from size \(a+b\) to \(r+t+2\). The matrices
  \(u'(Y)\) form the unipotent radical \(U'\) of the upper parabolic with
  exchanged blocks \((b, a)\), and \(P w U'\) is the open Bruhat cell
  \(P w N_0\): one has \(N_0 = N_{M'} U'\) with \(M' = w^{-1} M w\) and
  \(w N_{M'} w^{-1} = N_M\).
- `openCellHaar F r t` is `MeasureTheory.Measure.addHaar`, a fixed Haar
  measure on the locally compact group \(M_{b\times a}(\mathbb A) \cong
  U'(\mathbb A)\) with its Borel σ-algebra. Its normalization is not
  specified; every Haar measure is a positive multiple of it.
- `openCellIntegral ψ φ s` is
  \[
    I(\phi, s) = \int_{M_{b\times a}(\mathbb A)}
      W_M(\phi_s)\bigl(w\,u'(Y)\bigr)\,
      \overline{\psi_N\bigl(u'(Y)\bigr)}\,dY,
    \qquad \phi_s(g) = \phi(g)\,H(g)^s ,
  \]
  where \(H(g)^s\) is Shahidi's power `heightPower F r t s g`.

## Proved facts

- `openCellUnipotent_apply` writes the entries of \(u'(Y)\) as those of
  `Shahidi.upper (t+1) (r+1) (Adeles F) Y`.
- `openCellUnipotent_superdiagonal` shows that the only superdiagonal entry
  of \(u'(Y)\) that can be nonzero is \(Y_{t,0}\), at position
  \((t, t+1)\).
- `openCellUnipotent_superdiagonal_sum` concludes
  \(\sum_i u'(Y)_{i,i+1} = Y_{t,0}\); hence the character in the integrand is
  \(\overline{\psi_N(u'(Y))} = \overline{\psi(Y_{t,0})}\).

## Source

Shahidi, *Functional equation satisfied by certain L-functions*, Compositio
Math. 37 (1978), Lemma 2.1, (2.10), p. 181, works with right
\(G_F\)-invariant functions and the sum over \(G_F/P_F\). It writes the
Fourier coefficient of the Eisenstein series as
\[
  \int_{u\in {}^\circ U_{\mathbb A}/{}^\circ U_F}\;
  \int_{u'\in N_{\mathbb A}}
  \Phi_s(g\,u'\,w_0\,u)\,\overline{\chi(uu')}\,du'\,du .
\]
The inner variable \(u'\) runs over the adelic points of the unipotent
radical \(N\) of \(P\), which parametrizes the open cell \(N w_0 P\) in
this right-invariant convention. The outer variable \(u\) runs over the right
quotient \({}^\circ U_{\mathbb A}/{}^\circ U_F\) of the unipotent subgroup
\({}^\circ U\) coming from the Levi factor. In the proof, p. 182, the
contribution of a single Bruhat cell is written as
\(\int_{u'\in N^V_{\mathbb A}}\int_{u\in V_{\mathbb A}/V_F}
\Phi_s(g\,u'\,u\,w)\,\overline{\chi(u)}\,\overline{\chi(u')}\,du\,du'\),
with the integral over the quotient \(V_{\mathbb A}/V_F\) inside the
integral over the radical. Shahidi, *On certain L-functions*, Amer. J. Math.
103 (1981), proof of Theorem 5.1, p. 351, applies the lemma ("Lemma 2.1 and
computations in Section 4 of [23]").

The Library series is left \(\mathrm{GL}_N(F)\)-invariant and sums over
\(P(F)\backslash G(F)\). The substitution \(g \mapsto g^{-1}\) passes
between the two conventions. It turns right quotients into left quotients and
replaces the Weyl representative by its inverse. It also replaces the
character \(\chi\) by \(\chi^{-1}\): the coefficient `coeff` for
\(\psi_N\) corresponds to Shahidi's coefficient for \(\chi = \psi_N^{-1}\).
In the left-invariant form the open cell is \(P w N_0 = P w U'\) for the
Library representative \(w\), with \(N_0 = N_{M'}U'\) and
\(w N_{M'} w^{-1} = N_M\). Its term is
\(\int_{N_{M'}(F)\backslash N_0(\mathbb A)} \phi_s(w n)\,
\overline{\psi_N(n)}\,dn\). Write \(n = n'u'\) with \(n' \in N_{M'}\) and
\(u' \in U'\). Then \(w n' = u w\) with \(u = w n' w^{-1} \in N_M\), and
\(\psi_N(n') = \psi_N(u)\). On the half-plane of absolute convergence,
Fubini's theorem puts the Levi integral inside:
\[
  \int_{U'(\mathbb A)}\int_{N_M(F)\backslash N_M(\mathbb A)}
  \phi_s(u\,w\,u')\,\overline{\psi_N(u)}\,\overline{\psi_N(u')}\,du\,du' .
\]
The inner integral is \(W_M(\phi_s)(w u')\), so this is \(I(\phi, s)\) for
the Haar measure on \(U'(\mathbb A)\) giving \(U'(F)\backslash U'(\mathbb A)\)
mass one.

The local coordinates \(w\) and \(u'(Y)\) follow Shahidi, *Fourier
transforms of intertwining operators and Plancherel measures for GL(n)*, Amer.
J. Math. 106 (1984), printed page 72, (0.2).
