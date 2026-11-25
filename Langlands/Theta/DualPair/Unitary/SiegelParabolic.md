# The operators of the Siegel parabolic

**GKT Lemma 2.16** (p. 58) and **Corollary 2.18** (p. 60) for the image `g ⊗ 1_V` of the Siegel
parabolic of `U(ν, ν)`, times the value `β(m(a) n(b)) = χ(det a)` of the Leray splitting
(Proposition 12.29, p. 375): the first two formulas of **Proposition 12.27 (1)** (p. 372) in Case
`3₊`.

The module `Langlands.Theta.DualPair.Unitary.SiegelParabolic` defines the operators by which the
Siegel parabolic subgroup of `U(ν, ν)` acts in the Leray splitting, and proves their properties
(internal lemmas).

## Content

- `siegelParabolicOp c ψ χ Q g φ x = splittingScalar F χ |α| (det A) · ψ(½ β(x A, x B)) · φ(x A)` for
  `g = [[A, B], [C, D]]` and `β` the Hermitian pairing (`Langlands/Theta/DualPair/Unitary/Form.lean`).
  It is used for `g` in the Siegel parabolic (`C = 0`): for `g = diag(a, c(a)⁻ᵀ)` it is
  `φ ↦ χ(det a)|N det a|^{|α|/2} φ(· a)`, for `g = [[1, b], [0, 1]]` multiplication by the character
  of second degree `x ↦ ψ(½ β(x, x b))`.

Internal lemmas (namespace `Langlands.Theta.Unitary.Internal`), for an invertible Hermitian `Q`, a
continuous non-trivial unitary `ψ` and `χ` with the condition of the splitting scalar:
`parFun_sieg_mul` (the operators of the Siegel parabolic form a representation: `1 ↦ id`,
`p q ↦` the composition, from the block relations of the Siegel parabolic, the multiplicativity of
the splitting scalar and `β(x a, y) = β(x, y c(a)ᵀ)`), `parFun_mem` (they preserve Schwartz–Bruhat
functions), `heisFun_parFun` (they normalize the Schrödinger operators: `ρ(w) T(p) = T(p) ρ(w p)`),
`parFun_lintegral_sq` (they preserve `∫ |φ|²` for every Haar measure, since
`|splittingScalar(det A)|² = |N det A|^{|α|}` compensates `x ↦ x A`, `map_mul_mul_addHaar`), and
`parFun_fixed_near_one` (for a Schwartz–Bruhat `φ`, `T(p) φ = φ` for `p` near `1` in the Siegel
parabolic). These are the explicit formulas of Kudla, *Splitting metaplectic covers of dual
reductive pairs*, Israel J. Math. 87 (1994), 361–401, §5, p. 400 (the operators `ω_V(g)` of the
Schrödinger model, with `β_V` of Theorem 3.1, p. 378), for the Siegel parabolic. Kudla writes one
formula for all `g ∈ U(W)`, with Haar measures normalized as in Rao's paper (not in the library);
the factor `|N det A|^{|α|/2}` is not written out there.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean`, lines 125–128
(`parFun`); under `Proofs/DivisorProofs/`: `ParFunSiegMul.lean`,
`SiegelParabolicPreservesSchwartzBruhat.lean`, `SiegelParabolicOperatorsHeisenbergCompat.lean`,
`LintegralSqSiegelParabolicOperatorEq.lean`, `SchwartzBruhatFixedNearOneSiegelParabolic.lean` (each
whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `KSp.parFun` → `Langlands.Theta.siegelParabolicOp` (public); the lemmas keep their source names
  in `Langlands.Theta.Unitary.Internal` (`ParNear` helpers as `Unitary.Internal.ParNear`).
- The wrappers `parFun_sieg_mul'`, `siegelParabolic_preserves_schwartzBruhat`,
  `siegelParabolic_operators_heisenberg_compat`, `lintegral_sq_siegelParabolicOperator_eq`,
  `schwartzBruhat_fixed_near_one_siegelParabolic` are not taken; calls of the wrappers of other files
  are replaced by calls of the wrapped lemmas, in particular `splitUnitarySiegelParabolic_block_relations`
  by `UnitaryGroup.exists_eq_siegelLevi_mul_siegelUnipotent` and
  `map_twoSided_mul_haar_matrix_quadraticExt` by `map_mul_mul_addHaar`.
- `IsHerm`, `ResEtaPow` stay as internal hypotheses; `hE.invol` (a function `∀ z, c (c z) = z`) is
  `hE.involutive` (`Function.Involutive c`).

## Declarations

- `Langlands.Theta.siegelParabolicOp`

## Dependencies

`Langlands.Theta.DualPair.LerayCharacter`, `Langlands.Theta.DualPair.Unitary.Schrodinger`,
`Langlands.Group.Unitary.BigCell`.
