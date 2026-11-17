# The Langlands quotient of a Langlands-ordered real standard module

Lean module: `Langlands.Representation.Archimedean.RealLeviLanglandsQuotient`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states and proves `Langlands.Archimedean.RealLeviLanglandsQuotientStatement` (proof
`realLeviLanglandsQuotient`). This is the last step of the single-shot Langlands-quotient
argument along the standard parabolic subgroup `Q` of the tie classes. It derives
`RealStandardLanglandsQuotientStatement` from three statements that are not yet proved:
`RealLeviChartIntegrableStatement`, `RealLeviParabolicIntegrationStatement` and
`RealTemperedStandardIrreducibleStatement`. These three are hypotheses of the statement. No
literature statement is claimed and nothing is cited; the provenance is internal ("derived").
The conclusion is the Library statement `RealStandardLanglandsQuotientStatement`; its own
provenance is described in the Markdown of `RealLargeLanglandsQuotientReduction`.

The module imports `RealTieClasses` (namespace `Langlands.Archimedean.RealTieClasses`), which
Worker 5 wrote for Task 7069. It is included in this candidate unchanged from their draft for
Task 7069 (revision 2), with its own Markdown file `RealTieClasses.md`. Only its theorem
`RealTieClasses.exists_tieData` is used here.

Unprefixed names below are in the namespace
`Langlands.Archimedean.RealLeviLanglandsQuotient`.

## Notation

As in `RealLeviDensity.md` and `RealLeviWitness.md`. For `dss : Fin c → List RealBlock`:
`sz dss i = realRank (dss i)`, `N = ∑_i sz dss i`, `flat dss = dss 0 ++ ⋯ ++ dss (c-1)`, and
`cl dss i` is the twisted class list of `RealLeviSlices`. `cls (sz dss) p` is the index of the
block of `Q` that contains the position `p`. `StdSpace N ds` is
`kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)` and `DualSpace N ds` is
`kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
(unitaryCompact ℝ N)` (both from `RealLeviDuality`). `annW W ⊆ DualSpace N ds` is the
annihilator of `W` for the pairing `∫_{O(N)} v w` (`RealLeviDensity.annW`, `mem_annW`).
`Θ(u, h) = RealLeviPairing.theta (slots ds N) u h` is the pairing of `RealLeviPairing.md`.
`IsGKSubmodule` and `IsIrreducibleGKModule` are as in `RealLargeLanglandsQuotientReduction`.

## The statement

`RealLeviLanglandsQuotientStatement` is the implication

`RealLeviChartIntegrableStatement → RealLeviParabolicIntegrationStatement →
RealTemperedStandardIrreducibleStatement → RealStandardLanglandsQuotientStatement`.

The conclusion `RealStandardLanglandsQuotientStatement` is the Library statement: for all
`n : ℕ` and `ds : List RealBlock` with `realRank ds = n` and `IsRealLanglandsOrdered ds`, there
is a submodule `R` of `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` such
that `R` is a `(𝔤, K)`-submodule (`IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds)
R`), `R ≠ ⊤`, and every `(𝔤, K)`-submodule `W ≠ ⊤` satisfies `W ≤ R`.

The three hypotheses are:

* `RealLeviChartIntegrableStatement` (module `RealLeviChartIntegralStatement`): chart
  integrability along standard parabolic subgroups;
* `RealLeviParabolicIntegrationStatement` (module `RealLeviParabolicIntegrationStatement`):
  the integration formula along standard parabolic subgroups;
* `RealTemperedStandardIrreducibleStatement` (Library module `RealTemperedIrreducibleStatement`):
  the standard module of a list of blocks whose block exponents are all equal is irreducible.

## Proof outline

Let `ds` be Langlands-ordered of rank `n`.

1. **Tie classes** (`RealTieClasses.exists_tieData`, using
   `RealTemperedStandardIrreducibleStatement`). There are `c` and `dss` with `flat dss = ds` such
   that the position block exponents of `ds` weakly decrease, strictly decrease from one block of
   `Q` (sizes `sz dss`) to a later one, and every class standard module (of `cl dss i`) is
   irreducible. Then `n = N` (`RealLeviSlices.realRank_flat`).
2. **The witness** (`realLeviWitness`). There are `O(sz_i)`-finite `φ_i` in the dual principal
   series of `cl dss i` and `h₀ ∈ StdSpace N ds` with `Θ(u, h₀) ≠ 0` for every `u ∈ DualSpace N ds`
   with the product coefficients of the `φ_i` (`RealLeviWitness.ProdCoeffs`).
3. **A reference vector** (`realLeviDensity` with `W = ⊥`; `⊥ ≠ ⊤` by `bot_ne_top`). Some
   `u₀ ∈ DualSpace N ds` has the product coefficients of the `φ_i`. Let `Λ = Θ(u₀, ·)`, a linear
   functional on `StdSpace N ds` (`thetaL`; additivity is `RealLeviPairing.theta_add`, which uses
   `RealLeviChartIntegrableStatement`).
4. **Proper submodules lie in `ker Λ`**. Let `W` be a proper `(𝔤, K)`-submodule and `w ∈ W`.
   `realLeviDensity` gives `u_W ∈ DualSpace N ds` that annihilates `W` and has the product
   coefficients of the `φ_i`. Then `∫_{O(N)} u_W(κ g) w(κ) dκ = 0` for all `g`
   (`integral_mul_eq_zero_of_annihilates`). So `Θ(u_W, w) = 0` by `realLeviLimit` (using
   `RealLeviChartIntegrableStatement` and `RealLeviParabolicIntegrationStatement`). Since `u₀` and
   `u_W` have the same jointly allowed coefficients (`RealLeviWitness.coeffs_eq_of_prodCoeffs`),
   `Λ(w) = Θ(u₀, w) = Θ(u_W, w) = 0` (`RealLeviPairing.theta_congr`).
5. **The largest proper submodule**. Let `R` be the supremum of all proper `(𝔤, K)`-submodules.
   It is a `(𝔤, K)`-submodule (`isGKSubmodule_iSup`) and contains every proper one. It lies in
   `ker Λ` by step 4. Since `Λ(h₀) ≠ 0` by steps 2 and 3, `h₀ ∉ R`, so `R ≠ ⊤`.

## Results

**Matrix coefficients of annihilators** (section `Annihilator`).

* `integral_mul_eq_zero_of_annihilates`: let `W` be a `(𝔤, K)`-submodule of `StdSpace N ds`, and
  let `u ∈ DualSpace N ds` satisfy `∫_{O(N)} u(κ) w(κ) dκ = 0` for all `w ∈ W`. Then
  `∫_{O(N)} u(κ g) w(κ) dκ = 0` for all `w ∈ W` and `g ∈ GL_N(ℝ)`. Proof: the image `U` of
  `annW W` in the functions on `GL_N(ℝ)` is stable under right translation by `O(N)`
  (`RealLeviDensity.annW_rep`) and under right derivatives (`RealLeviDensity.annW_lie`), and it is
  orthogonal to `w` on `O(N)`. `u ∈ U` by hypothesis. Apply the Library lemma
  `JacquetDual.integral_mul_eq_zero_of_orthogonal` (signed-power position characters,
  `RealStrictCharacterLanglandsQuotient.isSignedPower`; `w` continuous).

**Assembly** (section `Assembly`).

* `thetaL hT1 hA hu`: for `u ∈ DualSpace N (flat dss)` with `N = ∑_j sz dss j`, the map
  `h ↦ Θ(u, h)` as a `ℂ`-linear map `StdSpace N (flat dss) →ₗ[ℂ] ℂ` (from
  `RealLeviPairing.theta_add` and `RealLeviPairing.theta_smul`). `thetaL_apply` unfolds it.
* `bot_ne_top`: if `realRank ds = N`, then `⊥ ≠ ⊤` in the submodules of `StdSpace N ds`. A
  nonzero vector is given by `RealLeviWitness.exists_std_ne_zero`.
* `isGKSubmodule_iSup`: the supremum of a family of `(𝔤, K)`-submodules is a
  `(𝔤, K)`-submodule (`Submodule.iSup_induction`).
* `exists_largest`: assume `RealLeviChartIntegrableStatement` and
  `RealLeviParabolicIntegrationStatement`. Let `dss` be such that the position block exponents of
  `flat dss` weakly decrease along the positions, strictly decrease from a block of `Q` to a later
  one (`cls (sz dss) p < cls (sz dss) q`), and every class standard module is irreducible. Then
  `StdSpace N (flat dss)` has a `(𝔤, K)`-submodule `R ≠ ⊤` that contains every proper
  `(𝔤, K)`-submodule. This is steps 2–5 of the proof outline; `R` is `⨆` over the subtype of
  proper `(𝔤, K)`-submodules.

`realLeviLanglandsQuotient`: step 1 (`RealTieClasses.exists_tieData`, then `subst` of
`flat dss = ds` and of `n = N`) followed by `exists_largest`.
