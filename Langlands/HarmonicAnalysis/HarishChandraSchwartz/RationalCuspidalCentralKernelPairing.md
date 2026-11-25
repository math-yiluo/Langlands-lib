# The VIII.4.1 pairing input from the VIII.3.2 integrability form

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, proof of Proposition VIII.4.1, printed pp. 329–330 (PDF pp. 95–96),
where the diagonal integral is made finite by VIII.3.2. Registered source
`waldspurger-2003-plancherel`.

This module continues the local kernel step `RationalCuspidalCentralKernelStep`.
It imports `RationalCuspidalCentralKernelDiagonal`, which imports
`RationalCuspidalCentralKernelStep`. It reduces the pairing input
`RationalLevelKernelPairingIntegrable` of `RationalCuspidalCentralKernelDiagonal` to
`RationalLevelKernelConjugationIntegrable`. That is the integrability of the
descended conjugation pairings of `E` with every Schwartz function: the
form of the VIII.3.2 conclusion at `f₁ = E`.

## Generic results

- The existing `Langlands.isInvInvariant_of_isMulRightInvariant`. On a locally compact group, a
  regular Haar measure `μ` that is also right invariant is invariant under
  inversion. The proof is the argument of Mathlib's
  `IsHaarMeasure.isInvInvariant_of_regular`. Since `μ` is right invariant,
  `μ.inv` is left invariant, so `μ.inv = c μ` by uniqueness
  (`isMulLeftInvariant_eq_smul_of_regular`). Applying inversion twice gives
  `μ = c² μ`; evaluating on a positive compact set gives `c² = 1`, hence
  `c = 1`.
- `quotientInv A` is the inversion `A g ↦ A g⁻¹` of `A \ G` for a normal
  subgroup `A`. It is defined through `normalLeftQuotientHomeomorph`, which
  identifies `A \ G` with the quotient group `G ⧸ A`. `quotientInv_mk` gives
  `quotientInv A (A g) = A g⁻¹`, and `continuous_quotientInv` gives continuity.
- `IsCompatible.measurePreserving_quotientInv`. Let `A` be closed and central
  in a locally compact, second countable, Hausdorff group `G`, with `μ_G`
  left invariant and `μ_A` a regular, right-invariant Haar measure. Then every
  compatible quotient measure `ν` on `A \ G` is preserved by `quotientInv A`.
  Proof. The image `μ'` of `ν` on `G ⧸ A` is `c μ₀` with `c ≠ 0` for the Haar
  measure `μ₀ = Measure.haar` (`IsCompatible.exists_smul_eq_map`). It is right
  invariant because `ν` is invariant under the right translations of `A \ G`
  (`IsCompatible.right_invariant`), and these correspond to right
  multiplication on `G ⧸ A`. So `μ₀` is right invariant, hence inversion
  invariant by the previous lemma, and so is `μ'`. Transporting back by the
  homeomorphism gives the claim.
- `rightCosetIndicator_mem_levelSubmodule`. Let `Ξ > 0` and `σ ≥ 0` be
  continuous, `H` a compact open subgroup and `a` central. Then the
  characteristic function `1_{H a}` lies in the level `C_H`. It is
  `H`-bi-invariant because `a` commutes with `H`. It is continuous because it
  is locally constant (`IsBiInvariant.isLocallyConstant`). It is supported in
  the compact set `H a`, so every `ν_r` is finite
  (`nu_lt_top_of_hasCompactSupport`).

## Rational results

- `rationalRightCosetIndicator hKc hPK ρ hs H hHc a` is `1_{H a}`, for a
  compact open `H` and `a ∈ A_G(F)`, as an element of the actual rational
  Schwartz space. `coe_rationalRightCosetIndicator` records its underlying
  function.
- `RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E` is the
  named hypothesis. Take any right-invariance instance on `muA`, any Borel
  structure on `A_G(F) \ G(F)`, any quotient measure `muQ` compatible with
  `muG` and `muA`, and any `f₂` in the actual Schwartz space. Then
  `rationalLeftConjugationPairing hKc hPK ρ s hs muG E f₂`, that is
  `q ↦ ∫ E(q̇ g q̇⁻¹) f₂(g) dmuG(g)`, is `muQ`-integrable. The published statement
  `RationalCuspidalConjugationIntegrabilityStatement` in
  `RationalCuspidalConjugationStatement` concludes this for every cuspidal
  `f₁`; this module retains that analytic proof obligation.
- `RationalLevelKernelPairingIntegrable.of_leftConjugationPairing` assumes a
  Haar `muA`, a Haar `muG` and a compact open `H`. It derives
  `RationalLevelKernelPairingIntegrable hKc hPK ρ muA muG H E` from
  `RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E`. For each
  `a`, it applies the hypothesis with `f₂ = 1_{H a}`. It then notes that the
  required function `q ↦ conjugationPairing muG E 1_{H a} (q̇⁻¹)` is the
  descended pairing composed with `quotientInv`, and it transports
  integrability by `IsCompatible.measurePreserving_quotientInv`
  (`MeasurePreserving.integrable_comp`).

## How the pieces compose

Assume:
- `E` satisfies `IsRationalCuspidalLevelKernel`;
- `G` is connected reductive and `muG` is a Haar measure;
- `χ` is trivial on `A_G(F) ∩ H`;
- `RationalLevelKernelConjugationIntegrable` holds.

Then this module, `IsRationalCuspidalLevelKernel.diagonalIntegrable`
(`RationalCuspidalCentralKernelDiagonal`) and
`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan` (`RationalCuspidalCentralKernelStep`, with
the weight hypotheses) give finite dimensionality of the actual level span.

## Open hypotheses

- `RationalLevelKernelConjugationIntegrable`: VIII.3.2
  (`RationalCuspidalConjugationIntegrabilityStatement`, not proved in the Library).
- For the composition with `RationalCuspidalCentralKernelStep` and
  `RationalCuspidalCentralKernelDiagonal`:
  - `IsRationalCuspidalLevelKernel`: from the rank adapter (`RationalCuspidalUnit`,
    `RationalCuspidalUnitKernel`) and the laws of the VIII.2 degree-zero projection;
  - `CentralWeights`: from `RationalSplitCenterHeightStatement`, proved as
    `rationalSplitCenterHeight`;
  - `L2Weights` and `ConvolutionWeights`: Lemma II.1.5. Its upper-bound input
    `RationalXiUpperBoundStatement` is proved as `rationalXiUpperBound`. Its
    basis/Cartan structural premises belong to the closed assembly of the
    target, as detailed in `RationalCuspidalCentralKernelStep`.
  - Unimodularity of `G(F)` is proved
    (`rationalHaar_isMulRightInvariant`).

Nothing here assumes same-rank finiteness, same-rank reconstruction, the
closed target or a dimension bound.
