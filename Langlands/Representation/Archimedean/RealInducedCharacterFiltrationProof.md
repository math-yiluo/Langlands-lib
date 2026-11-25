# Proof of `RealInducedCharacterFiltrationStatement`

Lean module: `Langlands.Representation.Archimedean.RealInducedCharacterFiltrationProof`, namespace
`Langlands.Archimedean.RealInducedCharacterFiltrationProof`.

## Result

`realInducedCharacterFiltration : RealInducedCharacterFiltrationStatement`.

The statement is the Library's `Langlands.Archimedean.RealInducedCharacterFiltrationStatement`
(module `RealInducedPairFiltrationReduction`). Let `d : ComplexCharacterData` be a complex
character of weight `m` and exponent `t`; it gives the induction block `RealBlock.induced d`
of size 2. Let `c : RealCharacterData` be a real character `sgn^ε |·|^s`. If
`Re t < Re s`, then the standard module on `GL₃(ℝ)` of `[induced d, character c]` has the
filtration `RealAdjacentFiltration 3 [] [] (RealBlock.induced d) (RealBlock.character c)`.

This file contains only the final assembly. The proof is internal to this project. The case analysis and the analytic lemmas are not taken from a literature proof.

## Declaration

`realInducedCharacterFiltration` applies
`RealInducedCharacter.realInducedCharacterFiltration_of_landing` (module
`RealInducedCharacterFiltration`) to two proofs:

* `RealSwapLandingIntegral.inducedFirst : RealSwapLandingInducedFirstStatement` (module
  `RealSwapLandingIntegral`);
* `RealSwapLandingMirror.characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst :
  RealSwapLandingCharacterFirstStatement` (module `RealSwapLandingMirror`).

The two landing statements are defined in module `RealSwapLandingStatement`.

## Route of the whole proof

Notation: `ℓ = |m|`, `a = t + ℓ/2` and `b = t - ℓ/2`. The standard module of `[d, c]` is the
subspace of the principal series of `(sgn^{ℓ+1}|·|^a, |·|^b, c)` on which the left Fourier
coefficients `Φ^0_k` along the rotation `r_0` vanish for `|k| < ℓ`.

1. **Case analysis** (module `RealInducedCharacterFiltration`). It assumes the two landing
   statements.
   - `ℓ = 0`: `RealStandardFiltration.realAdjacentFiltration_induced_character_of_weight_eq_zero`
     reduces to the two-character filtration `realCharacterPairFiltration` (Library).
   - `ℓ > 0` and `s - a` not a negative integer: the pushforward of module
     `RealInducedCharacterPushforward`, through the tail maps of module
     `RealInducedCharacterMaps` (block `d` replaced by the two characters `c_a`, `c_b`).
     It needs the mirror landing `RealInducedCharacter.highModes_eq_zero_mirror` of module
     `RealInducedCharacterLanding`, which uses the induced-first statement.
   - `ℓ > 0` and `s - a = -m'` with `m' ≥ 1` (then `2m' < ℓ`): module
     `RealInducedCharacterHard`. It builds a bijective exact intertwiner between the
     standard modules of `[c, d]` and `[d, c]` from a tail map and a generic swap. Which
     landing statement it uses depends on the parity. Injectivity comes from the uncertainty
     principle `RealOrthogonalUncertainty.realOrthogonalBlockUncertainty` and surjectivity
     from the `K`-type count of module `RealKTypeTransport` (both Library).

   The intertwining operators are the block Frobenius maps of the Library modules
   `RealBlockPositionData` and `RealBlockFrobeniusMap`. The landing statements show that
   composites of two such maps along `r_0` and `r_1` land in a standard module, not only in
   the principal series.
2. **Landing, induced-first half** (`RealSwapLandingIntegral.inducedFirst`). Module
   `RealSwapLandingAlgebra` reduces the statement to its special case `SpecialLanding`, with
   explicit sine-power multipliers. Module `RealSwapLandingIntegral` proves `SpecialLanding`
   with a chart integral over `ℝ²`. The helper modules are `RealSwapLandingKernel`,
   `RealSwapLandingRankOne` and `RealSwapLandingMatrices`.
3. **Landing, character-first half** (`RealSwapLandingMirror.characterFirst_of_inducedFirst`).
   Left translation by `κ₀ = diag(1, -1, 1) J`, combined with a determinant-sign twist,
   exchanges `r_0` and `r_1` and transports the induced-first half.

Each module named above has its own paired Markdown file, which states its results and
explains its proofs. The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
