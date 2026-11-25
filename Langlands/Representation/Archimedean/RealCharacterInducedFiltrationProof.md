# Proof of `RealCharacterInducedFiltrationStatement`

Lean module: `Langlands.Representation.Archimedean.RealCharacterInducedFiltrationProof`, namespace
`Langlands.Archimedean.RealCharacterInducedFiltrationProof`.

## Result

`realCharacterInducedFiltration : RealCharacterInducedFiltrationStatement`.

The statement is the Library's `Langlands.Archimedean.RealCharacterInducedFiltrationStatement`
(module `RealInducedPairFiltrationReduction`). For a real character `c = sgn^ε |·|^s`
(`RealCharacterData`) and a complex character `d` of weight `m` and exponent `t`
(`ComplexCharacterData`, giving the induction block `RealBlock.induced d` of size 2), with
`Re s < Re t`, the standard module on `GL₃(ℝ)` of `[character c, induced d]` has the filtration
`RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d)`.

This file contains only the final assembly. The proof is internal to this project: the case
analysis and the analytic lemmas below are not taken from a literature proof.

## Declarations

- `realSwapLanding : RealSwapLandingStatement`. The landing statement is the conjunction of
  `RealSwapLandingInducedFirstStatement` and `RealSwapLandingCharacterFirstStatement` (module
  `RealSwapLandingStatement`). The first half is `RealSwapLandingIntegral.inducedFirst`. The
  second half is `RealSwapLandingMirror.characterFirst_of_inducedFirst` applied to the first.
- `realCharacterInducedFiltration : RealCharacterInducedFiltrationStatement`. It applies
  `RealCharacterInducedFiltration.realCharacterInducedFiltration_of` to `realSwapLanding` and to
  `RealOrthogonalUncertainty.realOrthogonalBlockUncertainty :
  RealOrthogonalBlockUncertaintyStatement`.

## Route of the whole proof

Notation: `ℓ = |m|`, `b = t - ℓ/2` and `w = b - s`. The standard module of `[c, d]` is the
subspace of the principal series of `(c, sgn^{ℓ+1}|·|^{t+ℓ/2}, |·|^{t-ℓ/2})` cut out by the
vanishing of the left Fourier coefficients `Φ^1_k` along the rotation `r_1` for `|k| < ℓ`.

1. **Case analysis** (`RealCharacterInducedFiltration.realCharacterInducedFiltration_of`). It
   takes the landing statement and the uncertainty statement as hypotheses.
   - `ℓ = 0`: `RealStandardFiltration.realAdjacentFiltration_character_induced_of_weight_eq_zero`
     (module `RealCharacterInducedWeightZero`) reduces to the filtration for two characters,
     `realCharacterPairFiltration` (module `RealCharacterPairFiltration`).
   - `ℓ > 0` and `w` not a nonzero integer: `RealCharacterInducedPushforward.filtration_generic`.
   - `ℓ > 0` and `w` a positive integer: `RealCharacterInducedPushforward.filtration_reducible`.
   - `ℓ > 0` and `w = -m₀` with `m₀` a positive integer: then `m₀ < ℓ` because `Re s < Re t`.
     `RealCharacterInducedSwap.filtration_tail_first` or `filtration_tail_second` applies,
     according to the parity of `m₀ + ε`. These two use the uncertainty statement and the
     `K`-type count of module `RealKTypeTransport`.

   The intertwining operators are the block Frobenius maps of modules `RealBlockPositionData`
   and `RealBlockFrobeniusMap`. The landing statement shows that their composites map the
   standard module into the standard module, not just into the principal series.
2. **Landing, induced-first half** (`RealSwapLandingIntegral.inducedFirst`). Module
   `RealSwapLandingAlgebra` reduces the statement to `SpecialLanding`: the case of the explicit
   sine-power multipliers, for every shift `n`. This uses polynomial continuation in the
   multipliers. Module `RealSwapLandingIntegral` proves `SpecialLanding` with an explicit chart
   integral over `ℝ²`. The integral converges after the exponent of `c` is moved into the
   strictly dominant range by principal series extension. The helper modules are
   `RealSwapLandingKernel` (sine-power kernels and their Fourier multipliers),
   `RealSwapLandingRankOne` (the rank-one cotangent substitution) and `RealSwapLandingMatrices`
   (explicit matrices of `GL₃(ℝ)`).
3. **Landing, character-first half** (`RealSwapLandingMirror.characterFirst_of_inducedFirst`).
   It conjugates by `κ₀ = diag(1, -1, 1) J`, which exchanges `r_0` and `r_1`, and
   transports the induced-first half.
4. **Uncertainty** (`RealOrthogonalUncertainty.realOrthogonalBlockUncertainty`). It
   is proved by an `sl₂` lowest-weight argument on the finite-dimensional spaces of polynomial
   functions on `O(3)`, together with a parity reduction.

Each module named above has its own paired Markdown file, which states its results and proofs.
The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
