# Henniart's segment-head factor formulas: proof

Author: Worker 5047. The smooth-dual transport
`segmentHeadContragredientLFactor_of_lFactor` is reused unchanged from the
shared draft of this task by Worker 1738 (a worker of the previous project
instance).

This module, in namespace `Langlands.RankinSelberg`, proves the unchanged
Library proposition `SegmentHeadFactorStatement.{uF, uV, uW}` (module
`SegmentFactorStatement`), with independent field universe `uF` and base-carrier
universes `uV`, `uW`. It also proves each of the three components separately.
The segment heads keep the statement's carriers in `max uF uV` and
`max uF uW`. No hypothesis is added: the canonical p-adic topology, the
normalized upper-block segment induction behind `IsSegmentHead`, the supplied
unitary additive character `ψ` and the supplied self-dual Haar measure
(`SelfDualHaar`) are exactly those of the statement.

## Source

Henniart, *Une caractérisation de la correspondance de Langlands locale pour
GL(n)*, Bull. SMF 130 (2002), §2.6, printed page 595 (PDF page 9), registered
as `henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
Worker 5047 reread the page's text layer. Its three displays are, for
`(ρ, n), (ρ', n')`:

1. `L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`,
   `j = 1, …, min(n, n')`;
2. `L(s, St_n(ρ)^∨ × St_n'(ρ')^∨) = ∏_j L(s, ν^(1-j) ρ^∨ × ρ'^∨)`, same `j`;
3. `γ(s, St_n(ρ) × St_n'(ρ'), ψ) = ∏_(i=1)^n ∏_(j=1)^(n') γ(s, ν^(i+j-2) ρ × ρ', ψ)`.

Henniart derives them from the computations of Jacquet, Piatetski-Shapiro and
Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983)
(`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`):
Theorem (8.2), printed pages 444–445, for the L-factors, and gamma
multiplicativity, Theorem (3.1), printed pages 404–405, for the gamma factor.
The Library statements use zero-based indices, so the Lean exponents are
`n + n' - 2 - j`, `-j` and `i + j`; the paired statement Markdown explains this
shift and the printed omission of `∨` on `ρ` in the identity
`St_n(ρ)^∨ ≃ St_n(ν^(1-n) ρ^∨)` preceding the displays.

## Declarations and implemented proof

- `segmentHeadLFactor : SegmentHeadLFactorStatement.{uF, uV, uW}` (first
  display). The published reduction
  `segmentHeadLFactor_of_squareIntegrable` (module
  `SegmentHeadLFactorReduction`) derives the statement from JPSS Theorem (8.2),
  `SquareIntegrableLFactorStatement`, at the two universe orders
  `.{uF, uV, uW, max uF uV, max uF uW}` and
  `.{uF, uW, uV, max uF uW, max uF uV}`. Both premises are supplied by the
  published theorem `squareIntegrableLFactor` (module
  `SquareIntegrableLFactorProof`), which proves
  `SquareIntegrableLFactorStatement` for five arbitrary independent universes.
  The reduction realizes a head as an irreducible component of the centered
  JPSS induction of `ν^((n-1)/2) A`, applies (8.2) with the segment of larger
  degree first, uses JPSS (8.1)(i) when the base ranks differ, and moves the
  twists to the first member.
- `segmentHeadContragredientLFactor_of_lFactor`: the second display follows
  from the first. For a head `π` of `Δ` (length `m`), the published
  `IsSegmentHead.contragredient` (module
  `Classification.SegmentHeadContragredient`) makes the smooth contragredient
  `π.contragredient` a head of the endpoint-reversed segment `Δ.dual`, whose
  base is the dual of `ν^(m-1) ρ`. The representative of this base is
  `Av = twistedDualRep (-(m-1)) A`, the twist `|det|^(-(m-1)) A^∨` of the
  smooth dual of `A`: `dualClass_def`, `classContragredient_realPowerTwist` and
  `twistedDualRep_represents` prove `Δ.dual.base.IsRepresentedBy Av` at the
  level of isomorphism classes. The same is done for `σ`, `Δ'` (length `m'`)
  and `A'`. The first display for `(Δ.dual, Δ'.dual)` and the dual heads gives
  the head certificate `P`, the base certificates `Q j` and `P = ∏ j, Q j`.
  The certificate `Q j` is for
  `ν^(m+m'-2-j) ν^(-(m-1)) A^∨ × ν^(-(m'-1)) A'^∨`. The twist composition law
  `realPowerTwist_add` combines the first two twists, and
  `isPadicRankLPolynomial_realPowerTwist_move` moves the twist of the second
  member to the first. Since `m, m' ≥ 1`, the natural subtractions `m - 1`,
  `m' - 1` are cast to real subtractions, and
  `(m + m' - 2 - j) - (m - 1) - (m' - 1) = -j`. The polynomials and the
  product identity are kept unchanged.
- `segmentHeadContragredientLFactor :
  SegmentHeadContragredientLFactorStatement.{uF, uV, uW}`: the transport
  applied to `segmentHeadLFactor`.
- `segmentHeadFactor : SegmentHeadFactorStatement.{uF, uV, uW}`: the triple
  of `segmentHeadLFactor`, `segmentHeadContragredientLFactor` and the published
  `segmentHeadGammaFactor` (module `SegmentHeadGammaFactorProof`), which proves
  the third display from gamma multiplicativity, component comparison and
  determinant-twist transport.

Existence of every factor is part of the conclusions proved by the imported
theorems; no genericity, factor-existence, dual-compatibility or segment-formula
premise remains.

## Lean checks

`lean_check` (environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, the task's
pinned environment in this instance) of the module with declaration
`Langlands.RankinSelberg.segmentHeadFactor`: 0 errors, 0 warnings; universe
parameters `uF`, `uV`, `uW`; axioms `propext`, `Classical.choice`,
`Quot.sound`.
