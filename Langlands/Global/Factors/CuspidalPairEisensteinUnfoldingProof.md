# Proof of the unfolding of the generic coefficient

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingProof` proves

```lean
theorem Langlands.Global.cuspidalPairEisensteinUnfolding :
    CuspidalPairEisensteinUnfoldingStatement.{u}
```

The target is the proposition of
[CuspidalPairEisensteinUnfoldingStatement.md](CuspidalPairEisensteinUnfoldingStatement.md). Let
`F` be a number field with compact `𝔸_F / F`, let `T`, `T'` be cuspidal realizations with
unitary central characters, and let `ψ` be a standard additive character. Then there is
`κ > 0` such that for every section `φ` (`IsSection T T' φ`) there is `σ` with

```text
coeff ψ φ s = κ · openCellIntegral ψ φ s        for all s with σ < Re s.
```

The proof uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. It does not use
`CuspidalPairEisensteinCoefficientStatement`, the local numerator statement, or the boundary
nonvanishing statement. The unitary central character hypotheses are not used either. The
constant `κ` depends only on `F`, `r` and `t`.

## Source

Shahidi, *Functional equation satisfied by certain L-functions*, Compositio Math. 37 (1978), Lemma
2.1, (2.10), p. 181, with its proof, (2.10.1)–(2.10.3) and the paragraph after (2.10.3), on pp.
181–182, and Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), proof of Theorem 5.1, p.
351. Shahidi (1978) works with a maximal parabolic subgroup `P = MN` of a split group of type `G₂`
and the unipotent radical `U` of a fixed Borel subgroup (§1, p. 173; §2, p. 176). The Lean proof
carries out the analogous argument for the two-block parabolic of `GL_N`, with the upper
unitriangular group `N₀` in place of `U`. It follows the source's route: unfold the Eisenstein sum
along the double cosets `P(F) \ GL_N(F) / N₀(F)`, show that the non-open cells vanish, and identify
the open cell with the Levi Whittaker coefficient. The differences are in detail. The source sums
over the right quotient `G_F/P_F`. The Library uses the left quotient `P(F) \ GL_N(F)`, which
corresponds to it under inversion `g ↦ g⁻¹`. The cells are indexed by row echelon pivot sets instead
of the classes `w ∈ W/W_M` of (2.10.3). In the source a non-open class vanishes because its inner
integral factors through the character integral over `(V_w)_𝔸 / (V_w)_F`, `V_w = U ∩ wNw⁻¹`. The
Lean proof takes one simple root group inside the analogue of `V_w` on which `ψ_N` is nontrivial and
proves the vanishing by Weil averaging. Neither argument uses the cuspidality of the inducing data.
The constant `κ` comes from an explicit comparison of Haar measures.

## Supporting modules

The proof is assembled from these modules, in import order:

1. [CuspidalPairEisensteinRowEchelon.md](CuspidalPairEisensteinRowEchelon.md): orbits of the
   upper unitriangular group on `P \ GL_n` over a field.
2. [CuspidalPairEisensteinUnfoldingCells.md](CuspidalPairEisensteinUnfoldingCells.md): cell
   representatives for the two-block parabolic, and root elements for the non-open cells.
3. [CuspidalPairEisensteinUnfoldingGroups.md](CuspidalPairEisensteinUnfoldingGroups.md):
   `N₀(𝔸)`, its rational points and the pattern subgroups `Λ_J`, which have finite covolume.
4. [CuspidalPairEisensteinUnfoldingVanishing.md](CuspidalPairEisensteinUnfoldingVanishing.md):
   vanishing by Weil averaging.
5. [CuspidalPairEisensteinUnfoldingSeries.md](CuspidalPairEisensteinUnfoldingSeries.md): the
   twisted section, normal convergence, the sum over the cells, and a uniform bound on
   `N₀(𝔸)`.
6. [CuspidalPairEisensteinUnfoldingCellIntegral.md](CuspidalPairEisensteinUnfoldingCellIntegral.md):
   unfolding one cell, and vanishing of the non-open cells.
7. [CuspidalPairEisensteinUnfoldingOpenGroups.md](CuspidalPairEisensteinUnfoldingOpenGroups.md),
   [CuspidalPairEisensteinUnfoldingOpenMeasure.md](CuspidalPairEisensteinUnfoldingOpenMeasure.md),
   [CuspidalPairEisensteinUnfoldingOpen.md](CuspidalPairEisensteinUnfoldingOpen.md): the open
   cell as a semidirect product, its normalized Haar measures, and the iterated integral.
8. [CuspidalPairEisensteinUnfoldingLevi.md](CuspidalPairEisensteinUnfoldingLevi.md) and
   [CuspidalPairEisensteinUnfoldingLeviIntegral.md](CuspidalPairEisensteinUnfoldingLeviIntegral.md):
   the inner integral is the Levi Whittaker coefficient.
9. [CuspidalPairEisensteinUnfoldingRadicalHaar.md](CuspidalPairEisensteinUnfoldingRadicalHaar.md)
   and
   [CuspidalPairEisensteinUnfoldingOpenCellIntegral.md](CuspidalPairEisensteinUnfoldingOpenCellIntegral.md):
   the constant `κ`, and the open cell.

The convergence input is `exists_summable_eisensteinTerm_bound` of module
`Langlands.Global.Factors.CuspidalPairEisensteinConvergence`.

## This module

- `genericChar_eq`: `genericChar ψ` is the Library's `genericCharacter F (r + t + 1) ψ 1`.
  `haarH_eq`: `haarH = (haar fd₀)⁻¹ • haar`.
- `whittaker_eq_setIntegral`: for a continuous `f` on `GL_(n+1)(𝔸)` that is left invariant
  under `GL_(n+1)(F)`, the Library's `generalLinearWhittakerFunction` at `1` is
  `c_(n+1) ∫_{fd₀} f(x) conj(ψ_(n+1)(x)) dx`, by
  `RankinSelbergGlobal.Unfolding.subgroupCharacterCoefficient_eq_setIntegral`.
- `coeff_eq_setIntegral`: with `n = r + t + 1` and `f = E(φ, s)`, which is continuous and
  `GL_N(F)`-invariant for `σ < Re s`, `coeff ψ φ s` equals
  `c_N ∫_{fd₀} E(φ, s)(x) conj(ψ_N(x)) dx`.
- `coeff_eq_openCellIntegral` (**the unfolding**): given `NormalBound φ σ`, `σ < Re s` and
  `haarN.map radicalCoord = κ • openCellHaar`, `coeff ψ φ s = κ · openCellIntegral ψ φ s`.
  1. `eisensteinSeries_eq_sum_cells` writes `E(φ, s)` on `N₀(𝔸)` as the finite sum over the
     cells `J` of the cell series. Each cell series times `conj(ψ_N)` is integrable on `fd₀`
     (`unfold_cell`), so the integral is the sum of the cell integrals.
  2. `unfold_cell` turns the integral of cell `J` into `∫_{cellDomain J} cellIntegrand J`.
     For `J ≠ J₀` it vanishes (`setIntegral_cellIntegrand_eq_zero`), so only the open cell
     remains (`Finset.sum_eq_single`).
  3. `c_N · haar = haarH` (`unipotentNormalizer_eq`, `haarH_eq`). The open-cell integral for
     `haarH` is `κ · openCellIntegral ψ φ s` by `setIntegral_cellDomain_openIndex`. The
     integrability for `haarH` follows from that for Haar measure.
- `cuspidalPairEisensteinUnfolding`: take `κ` from `exists_map_radicalCoord_haarN` and `σ`
  from `exists_normalBound`.
