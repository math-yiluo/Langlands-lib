# The open cell contributes the open-cell integral

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenCellIntegral` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) evaluates the contribution of the open cell
`J₀ = {0, …, t}` to the generic coefficient. The cell representative is `w = openCellWeyl F r t`.
The contribution is `κ · openCellIntegral ψ φ s`, with `κ` from
[CuspidalPairEisensteinUnfoldingRadicalHaar.md](CuspidalPairEisensteinUnfoldingRadicalHaar.md).
This is the two-block `GL_N` analogue of the open-cell term of Shahidi, *Functional equation
satisfied by certain L-functions*, Compositio Math. 37 (1978), proof of Lemma 2.1, paragraph after
(2.10.3), p. 182, and Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), proof of Theorem
5.1, p. 351.

## Contents

The two main results below assume that `φ` is a section (`IsSection T T' φ`) and that `ψ` is a
standard additive character of `𝔸` (`IsStandardAdditiveCharacter F ψ`). The section hypothesis
makes `φ_s` continuous and left invariant under `P(F)`. The character hypothesis gives
`|ψ| = 1` and the triviality of `ψ` on `F`.

- `openIndex r t`: the open cell `openPivots r t` as a `PivotIndex`. `toMat_radicalHom_eq`:
  the matrix of the radical element `Y` is `openCellUnipotent F r t Y`.
- `cellIntegrand_openIndex`: in the coordinates `diag(m) u'(Y)`, the unfolded integrand of the
  open cell is

  ```text
  φ_s(w diag(m) u'(Y)) conj(ψ_N(diag(m) u'(Y)))
    = leviIntegrand φ_s ψ (w u'(Y)) m · conj(ψ(Y_(t,0))).
  ```

  The proof uses `rational_cellRep_openPivots` (`γ_(J₀) = w`), `openCellWeyl_mul_leviHom`
  (`w diag(A, B) = leviPair B A · w`), `genericChar_leviHom` and `genericChar_radicalHom`.
- `setIntegral_fdM_cellIntegrand`: assume `IsSection T T' φ` and
  `IsStandardAdditiveCharacter F ψ`. Let `Y` be a radical coordinate such that
  `m ↦ cellIntegrand J₀ (diag(m) u'(Y))` is integrable on `fdM` for `haarM`. Then its integral
  over `fdM` is `leviWhittaker F r t ψ φ_s (w u'(Y)) · conj(ψ(Y_(t,0)))`. Since `|ψ| = 1`,
  `leviIntegrand` is integrable as well, and `setIntegral_fdM_eq_leviWhittaker` applies to the
  continuous, `P(F)`-invariant function `φ_s`.
- `openCellIntegral_eq`: `openCellIntegral ψ φ s` is the integral over `Y`, for
  `openCellHaar`, of `leviWhittaker F r t ψ φ_s (w u'(Y)) · conj(ψ(Y_(t,0)))`, by
  `openCellUnipotent_superdiagonal_sum`.
- `setIntegral_cellDomain_openIndex` (**the open cell**): assume `IsSection T T' φ` and
  `IsStandardAdditiveCharacter F ψ`, let `κ ≥ 0` satisfy
  `haarN.map radicalCoord = κ • openCellHaar`, and suppose that the open-cell integrand
  `cellIntegrand J₀` is integrable on `cellDomain J₀` for `haarH`. Then

  ```text
  ∫_{cellDomain J₀} φ_s(w x) conj(ψ_N(x)) dhaarH(x) = κ · openCellIntegral ψ φ s.
  ```

  By the `P(F)`-invariance of `φ_s` and the triviality of `ψ` on `F`, the integrand is left
  invariant under `Λ_(J₀)(F)` (`cellIntegrand_patternRational_mul`), and `cellDomain J₀` is a
  fundamental domain of `Λ_(J₀)(F)` (`existsUnique_mem_cellDomain`). By
  `setIntegral_eq_iterated_open` it is an iterated integral over `Y` and `m ∈ fdM`. The inner
  integral is integrable for almost every `Y` (`Integrable.prod_right_ae`) and equals the
  integrand of `openCellIntegral` there. Finally `integral_haarN_eq` changes `haarN` into
  `κ • openCellHaar`.
