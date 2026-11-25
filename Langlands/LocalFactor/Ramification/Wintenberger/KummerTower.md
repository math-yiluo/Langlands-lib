# The Kummer tower is arithmetically profinite

Module `Langlands.LocalFactor.Ramification.Wintenberger.KummerTower`, namespace
`Langlands.Ramification.Wintenberger`.

Let `F` be a `p`-adic field, `ϖ` a uniformizer and `πs` a compatible system of `p^n`-th roots of
`ϖ` in `AlgebraicClosure F.Carrier` (`Kummer.IsKummerRootSystem F ϖ πs`), and
`L = Kummer.kummerTower F πs = ⨆ n, F(πs n)`. With `F.Carrier` normed by its canonical spectral norm,
this file proves that `L/F` is an infinite arithmetically profinite extension in the sense of the
FontaineWintenberger library, and that Wintenberger's `ψ_{L/F}` is the identity up to the first
Kummer break `p e/(p − 1)`.

## Main statements

- `ord_eq_one_and_ramificationIndex_of_pow_eq`: for `p`-adic fields `F ⊂ K` with
  `[K : F] ≤ p ^ n`, a uniformizer `ϖ` of `F` and `β ∈ K` with `β ^ (p ^ n) = ϖ`,
  `K.canonicalTopologicalData.ord β = 1` and
  `K.canonicalTopologicalData.ramificationIndex = p ^ n * F.canonicalTopologicalData.ramificationIndex`;
  `finrank_eq_of_pow_eq`: then `[K : F] = p ^ n`.
- The stages in the separable closure: `sepClosureEquiv F`, `towerRoot F πs n`,
  `towerStage F πs n : FontaineWintenberger.FiniteIntermediateField F.Carrier
  (SeparableClosure F.Carrier)` (the field `F(πs n)`), the same field as a `p`-adic field
  `towerStagePadic F πs n`, its generator `towerStageRoot F πs n`, and the levels
  `towerLevel πs n = Kummer.kummerBreak (towerStagePadic F πs n)`, with
  `towerLevel_eq : towerLevel πs n = p ^ n * Kummer.kummerBreak F`,
  `towerStage_finrank : [F(πs n) : F] = p ^ n`, `towerStage_strictMono`.
- `towerStep_isElementaryStep (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
  FontaineWintenberger.IsElementaryStep F.Carrier (towerStage F πs n) (towerStage F πs (n + 1))
  (towerStage_le_succ πs hπ n) (towerLevel πs n)`.
- `kummerTower_isAPF (hπ) : FontaineWintenberger.IsAPF F.Carrier (kummerTower F πs)`.
- `kummerTower_not_finite (hπ) : ¬ Module.Finite F.Carrier (kummerTower F πs)`.
- `kummerTower_apfPsi (hπ) {u : ℝ} (hu : u ≤ Kummer.kummerBreak F) :
  FontaineWintenberger.apfPsi F.Carrier (kummerTower F πs) u = u`.

In these statements `F.Carrier` carries `F.canonicalNormedField`, `F.canonicalNormedAlgebra` and
the class `FontaineWintenberger.IsPerfectResidueLocalField` of `FieldClass` as local instances.

## Proofs

The stage computation repeats the argument by which the Library computes the ramification of its
Kummer stages: the normalized order of `ϖ` in `K` is `e_K/e_F`, the order of `β` is positive and
`e_K ≤ [K : F] e_F ≤ p^n e_F`.

Each step `F(πs (n+1)) / F(πs n)` is the extension of the stage `K_n` by a `p`-th root of the
uniformizer `πs n`. The Library proves, for every `p`-adic field and uniformizer, that the fixing
subgroup of such a step and the upper group at the first Kummer break generate the absolute Galois
group (`Kummer.kummerStepUpperSup`) and that every later upper group fixes the step
(`Kummer.kummerStep_upper_le_fixingSubgroup`). Applied to `K_n` (as the `p`-adic field
`towerStagePadic F πs n`) and to an embedding of the step into an algebraic closure of `K_n`, these
are the two conditions of `APF.isElementaryStep_of_absoluteUpper`.

The tower criterion of the FontaineWintenberger library
(`isAPF_iSup_iff_tendsto_of_isElementaryStep`, Wintenberger 1.4.2) then applies, the first field
being `F` itself. Its condition is that the transformed levels `φ_{K_n/F}(i_n)` tend to infinity;
by the sum formula `apfPhi_eq_sum_of_isElementaryStep` they are
`i_0/e_0 + Σ_{k<n} (i_{k+1} − i_k)/e_{k+1}`, where `e_k ≤ [K_k : F] = p^k` (the fundamental identity
`local_ramificationIdx_mul_inertiaDeg`), so each term is at least `(p − 1) i_0 / p = e_F` and the sum
is at least `n e_F`. The union in the separable closure is the image of `kummerTower F πs`, so the
latter is APF (`isAPF_algEquiv`). It is infinite because its stages have degrees `p^n`.

For `ψ`: the Library's `Kummer.kummerTowerLimitUpperSup` says that the fixing subgroup of `L` and
`G_F^{p e/(p−1)}` generate `G_F`, and `APF.apfPsi_eq_self_of_sup_eq_top` applies.

## Declarations used

From the Library: `Kummer.kummerBreak`, `Kummer.IsKummerRootSystem`, `Kummer.kummerTower`,
`Kummer.kummerStepUpperSup`, `Kummer.kummerStep_upper_le_fixingSubgroup`,
`Kummer.kummerTowerLimitUpperSup`, `Kummer.ord_pow`, `PadicField.ofField`,
`PadicField.ramificationIndex_mul_extensionResidueDegree`, `extensionDegree_suppliedAlgebra`,
`extensionResidueDegree_pos`, `ramificationIndex_mul_ord_relative_algebraMap`. From the
FontaineWintenberger library: `isAPF_iSup_iff_tendsto_of_isElementaryStep`,
`apfPhi_eq_sum_of_isElementaryStep`, `FiniteIntermediateField.ramificationIdx`,
`local_ramificationIdx_mul_inertiaDeg`, `spectralIntegerRing_finrank`, `isAPF_algEquiv`.

## Sources

Wintenberger 1983, §1.2 (arithmetically profinite extensions and `ψ_{L/K}`), §1.3 (elementary
extensions) and §1.4 (the tower of elementary extensions of an APF extension, the criterion 1.4.2
and the formula for the transformed levels). The break of each Kummer step is the Library's
theorem `Kummer.kummerStepUpperSup`, with the sources given on its page.
