# Unfolding the generic coefficient of a cuspidal-pair Eisenstein series

`Langlands.Global.CuspidalPairEisensteinUnfoldingStatement.{u}` states that
the generic Fourier coefficient of the Eisenstein series induced from an
actual cuspidal pair is, on a right half-plane, a fixed positive multiple of
the open-cell integral of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md). The
module states the proposition and does not prove it.

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`,
let `T : CuspidalOperatorRealization F r` and
`T' : CuspidalOperatorRealization F t` have unitary central characters, and
let `ψ` be a standard additive character (`IsStandardAdditiveCharacter`).
Then there is a real `κ > 0` such that for every `φ` with
`CuspidalPairEisenstein.IsSection T T' φ` there is a real `σ` with
\[
  \mathrm{coeff}(\psi, \phi, s) = \kappa \cdot I(\phi, s)
  \qquad (\operatorname{Re} s > \sigma),
\]
where `coeff ψ φ s` is the generic coefficient
\(\int_{N_0(F)\backslash N_0(\mathbb A)} E(\phi,s)(n)\,
\overline{\psi_N(n)}\,dn\) of
[CuspidalPairEisensteinSeries.md](CuspidalPairEisensteinSeries.md) and
\(I(\phi,s)\) is `openCellIntegral ψ φ s`.

The constant `κ` does not depend on `φ` or `s`. It compares Haar measures:
`coeff` and `leviWhittaker` use quotient measures of total mass one, while
`openCellIntegral` uses the unnormalized Haar measure `openCellHaar` on
\(U'(\mathbb A) \cong M_{(t+1)\times(r+1)}(\mathbb A)\). With the Haar
measure on \(U'(\mathbb A)\) for which \(U'(F)\backslash U'(\mathbb A)\) has
mass one, the identity holds with constant \(1\). The unitary central
character hypotheses are those of
`CuspidalPairEisensteinCoefficientStatement`, where this proposition is used.

## Source

Shahidi, *Functional equation satisfied by certain L-functions*, Compositio
Math. 37 (1978), Lemma 2.1, (2.10), p. 181, with its proof on pp. 181–182,
and Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), proof of
Theorem 5.1, p. 351. Shahidi's functions are right \(G_F\)-invariant with
twist parameter in a left half-plane. The Library's series is left
\(\mathrm{GL}_N(F)\)-invariant and the twist \(H(g)^s = \delta_P^{s/N}\)
converges on a right half-plane. The comparison of the two forms of the open
cell integral is in
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md).

## A route of proof

This describes the source argument; it is not part of the statement.

1. For \(\operatorname{Re} s\) large the series converges absolutely and
   locally uniformly (Mœglin–Waldspurger II.1.5; Shahidi (1978), p. 179).
   Since \(N_0(F)\backslash N_0(\mathbb A)\) is compact, the sum and the
   integral can be interchanged.
2. Bruhat decomposition: \(P(F)\backslash G(F)\) is the union over
   \(w\in W_M\backslash W\) of the sets \(P(F)\backslash P(F)wN_0(F)\), and each
   term unfolds to an integral over
   \((N_0\cap w^{-1}Pw)(F)\backslash N_0(\mathbb A)\) (Shahidi (1978),
   (2.10.1)–(2.10.3), pp. 181–182).
3. For the open cell, \(N_0 = N_{M'}U'\) with \(N_0\cap w^{-1}Pw = N_{M'}\)
   and \(wN_{M'}w^{-1} = N_M\), and the term is \(I(\phi, s)\) for the
   normalized measure.
4. The other cells contribute zero. On each, either \(\psi_N\) is nontrivial
   on a unipotent subgroup under which the integrand is invariant (Shahidi
   (1978), p. 182), or the inner integral is a degenerate Whittaker
   coefficient of the cuspidal inducing data on \(M\), which vanishes.
