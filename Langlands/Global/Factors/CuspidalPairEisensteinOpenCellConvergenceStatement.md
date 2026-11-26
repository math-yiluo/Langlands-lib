# Absolute convergence of the open-cell integral

`Langlands.Global.CuspidalPairEisensteinOpenCellConvergenceStatement.{u}` (module
`Langlands.Global.Factors.CuspidalPairEisensteinOpenCellConvergenceStatement`) is a
Prop-valued statement. The module states it and does not prove it.

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`, let `T`, `T'` be
actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with unitary central characters,
and let `ψ : AddChar (Adeles F) ℂ` satisfy `RankinSelbergGlobal.IsStandardAdditiveCharacter`.
For every `φ` with `CuspidalPairEisenstein.IsSection T T' φ` there is a real `σ` such that
for every `s` with `σ < Re s` the function

`Y ↦ openCellIntegrand ψ φ s Y = W_M(φ_s)(w u'(Y)) · conj(ψ_N(u'(Y)))`

is integrable on `M_((t+1)×(r+1))(𝔸)` for `openCellHaar F r t` (with the Borel σ-algebra
that `openCellHaar` and `openCellIntegral` use). The notation is that of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md) and
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md). The
half-plane may depend on `φ`.

## Source

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`),
proof of Theorem 5.1, pp. 351–352 (PDF pages 56–57): the factorization of the Fourier
coefficient into local factors holds "for `Re(s) > 1/2`" (p. 351, in Shahidi's
normalization of the parameter), and at an archimedean place the local component, given by
formula (4.2) of Shahidi, *Functional equation satisfied by certain L-functions*, Compositio
Math. 37 (1978) (`shahidi-1978-functional-equation`), "converges absolutely for `Re(s)`
large (it is dominated by the corresponding intertwining integral which converges for
`Re(s)` large)" (p. 352).

The domination is the following. For `g = n m k` with `n` in the unipotent radical of `P`,
`m = diag(m_1, m_2)` in the Levi and `k` in the standard maximal compact subgroup,
`W_M(φ_s)(g) = δ_P(m)^(1/2 + s/(r+t+2)) · W_(φ_k)(m)`, where `φ_k` is the Levi slice of `φ`
at `k`, a finite combination of products of cusp forms. Cusp forms are bounded and the Levi
Whittaker coefficient is an integral over a quotient of total mass one, so
`|W_M(φ_s)(g)| ≤ C δ_P(m)^(1/2 + Re s/(r+t+2))` with `C` independent of `g`. The integral of
the right side over `g = w u'(Y)` is the intertwining integral of the flat section
`δ_P^(1/2 + Re s/(r+t+2))`, which converges for `Re s` large (Langlands; see also
Mœglin–Waldspurger, II.1.6).

## Remarks

- The statement involves no spectral presentation and no finite set of places.
- The hypotheses of unitary central characters and the standard character are those of
  `CuspidalPairEisensteinLocalNumeratorStatement`. The domination above uses `|ψ| = 1` and
  the boundedness of the cusp forms, which holds because their central characters are
  unitary.
