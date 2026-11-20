# Vertical-strip bounds of continued cuspidal pair L-functions

Lean module: `Langlands.Global.Factors.CuspidalPairVerticalStripStatement`.

`CuspidalPairVerticalStripStatement` is the bound-in-vertical-strips clause of Getz–Hahn
(2024), Theorem 11.7.1, and Cogdell (2004), Theorem 4.1(2), separated from the continuation:
the continuation is a hypothesis. It is a premise of `CuspidalPairPoleReductionStatement`
and a proposition definition only.

## 1. Sources

| Source ID | Short name | Locators |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | GH (Ch. 11: PDF = printed + 11) | Theorem 11.7.1, p.309 (PDF 320) |
| `cogdell-2004-analytic-theory-gln` | Cog04 (PDF = printed + 3) | Theorem 4.1, p.219 (PDF 222); boundedness in vertical strips, pp.220–221 (PDF 223–224) |

**What the sources state.** GH Theorem 11.7.1: the Rankin–Selberg L-function of cuspidal
`π`, `π'` trivial on `A_GL` "is bounded in vertical strips". Cog04 Theorem 4.1(2): "the
extended function is bounded in vertical strips (away from its poles)". Cog04 pp.220–221
proves this for `m = n - 1` and `m = n` by writing `L(s, π × π')` as a finite sum of global
integrals (finite places: p.220; archimedean places: Stade and Jacquet–Shalika) and for the
other ranks refers to Gelbart and Shahidi (Cog04 reference [12]).

## 2. The statement

For a number field `F`, actual cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)`,
both trivial on the split components of their centres (`IsTrivialOnSplitCentre`), spectral
presentations `P`, `P'` with irreducible admissible finite components, finite pair L-data
`c`, archimedean parameters `dR`, `dR'`, `dC`, `dC'` of `T`, `T'`, and
`infiniteL(s) = ∏_v L(s, dR v × dR' v) ∏_w L(s, dC w × dC' w)` (the expression of
`CuspidalPairPoleStatement`): every `Λ : ℂ → ℂ` with `c.IsCompletedLFunction infiniteL Λ`
that is holomorphic on `ℂ ∖ {0, 1}` satisfies `IsBoundedInVerticalStrips Λ`, i.e. for all
`a ≤ b` and `ε > 0` it is bounded on `a ≤ Re s ≤ b` outside the discs of radius `ε` about
`0` and `1`.

## 3. Match with the source

- By uniqueness of continuation, a `Λ` as in the hypothesis is the continued completed
  L-function on `ℂ ∖ {0, 1}`; the values at `0`, `1` are irrelevant to the conclusion. So
  the statement is the source's bound for the continued function. If the completed
  L-function had other poles the hypothesis would be empty; GH 11.7.1 shows it has none.
- "Away from its poles" is rendered by excluding discs about `0` and `1`, the only possible
  poles (GH 11.7.1). The vocabulary (`FinitePairLChoice`, `IsCompletedLFunction`,
  `IsBoundedInVerticalStrips`, `IsTrivialOnSplitCentre`) is that of
  `CuspidalPairPoleStatement`, whose Markdown explains the normalizations.
