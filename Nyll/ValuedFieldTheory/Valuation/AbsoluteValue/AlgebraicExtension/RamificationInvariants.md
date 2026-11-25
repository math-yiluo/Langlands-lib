# The fundamental inequality `e f ≤ [L:K]` and the identity `e f = [L:K]`

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` and `w` be real exponential (additive) valuations on fields `K ⊆ L`, with `w` restricting exactly to `v`. The file defines the ramification index `e` and the residue degree `f` intrinsically. It proves `e f ≤ [L:K]` for every finite extension. It proves equality for a finite separable extension of a discretely valued base that is henselian in the library's factorization sense; completeness is not assumed.

## Definitions

- `exponentialValuationRingMap`: the local ring map `𝒪_v → 𝒪_w`.
- `exponentialValueSubgroup v`: the value group `v(K^×)` as a subgroup of `ℝ`.
- `ExponentialValueGroupQuotient v w`: the quotient `w(L^×)/v(K^×)`.
- `exponentialRamificationIndex v w`: the cardinality (`Nat.card`) of this quotient.
- `exponentialResidueDegree v w hExt`: the `finrank` of the residue field extension.
- `DistinctExponentialValueCosetRepresentatives`: elements of `L^×` lying in pairwise distinct classes of `w(L^×)/v(K^×)`, stated by cross-multiplication with elements of `K^×`.

## Main results

- `ramificationInvariants_fundamental_inequality`: `e · f ≤ [L:K]` for `L/K` finite.
- Linear independence: products `ω_j π_i` of lifts of linearly independent residues and representatives of distinct value cosets are linearly independent over `K` (`ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent`, with an `_arbitrary` version for infinite index sets).
- `ramificationInvariants_fundamental_identity_of_discrete_of_separable`: for `L/K` finite separable, `v` discrete (`DiscreteExponentialValuation`) and the valuation of `𝒪_v` henselian (`HenselianValuationByFactorization`), `[L:K] = e · f`.
- `exponentialValuationSubring_eq_integralClosure_of_henselian`: for `L/K` algebraic and `v` henselian, `𝒪_w` is the integral closure of `𝒪_v` in `L`.
- Comparisons with Mathlib: `e = Ideal.ramificationIdx'` when both valuation rings are DVRs (`exponentialRamificationIndex_eq_ideal_ramificationIdx`), and `f = inertiaDeg` (`exponentialResidueDegree_eq_ideal_inertiaDeg`). Also, `v` is discrete if `𝒪_v` is a DVR.
- Lemmas `associatedAbsoluteValue_...` relate `v` to its associated absolute values.

## Proofs

For the inequality, a nontrivial residue combination of lifts is a unit, so inner sums take values in `v(K^×)`. A sum over distinct cosets therefore cannot vanish. The same argument shows that both index sets are finite.

For the identity, `𝒪_w` is identified with the integral closure, using the norm-formula and unique-extension theorems. The integral closure is a finite Dedekind extension of the DVR `𝒪_v` and not a field, so it is a DVR. Mathlib's formula `∑ eᵢ fᵢ = [L:K]` then applies with a single prime.

## Points to watch

- Exponential valuations, their discreteness and henselianity by factorization are the library's own notions. The henselian hypothesis stands for Hensel's lemma.
- `e` and `f` are `Nat.card` and `finrank`, which are `0` for an infinite quotient and for an infinite-dimensional residue extension. For finite `L/K` the inequality proof shows both are finite.
- Extension means exact equality `w ∘ algebraMap = v`.

The module comment says the inequality proof follows "pp. 149–150" of a source it does not name.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/RamificationInvariants.lean`: the Lean file is the source byte for byte (SHA-256 `a5c30b3ec4589edf887e91bd8b1957d7658377094098b8103ac0d99106efcf33`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
