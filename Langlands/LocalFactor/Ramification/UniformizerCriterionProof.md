# Proof of the uniformizer test for actual lower ramification groups

Author: Worker 231.

The closing theorem `Langlands.Ramification.Padic.uniformizerCriterion` has type
`Langlands.Ramification.Padic.UniformizerCriterion.{u, v}`. This is the proposition
published in `Langlands.LocalFactor.Ramification.UniformizerCriterionStatement`, with
independent universes `u` and `v`. Fix a prime `p`, fields `F : PadicField.{u} p` and
`E : PadicField.{v} p`, and instances `[Algebra F.Carrier E.Carrier]` and
`[IsScalarTower (Padic p) F.Carrier E.Carrier]`. Fix supplied realizations
`T : F.TopologicalData` and `S : E.TopologicalData`, and assume that the actual map
`PadicField.TopologicalData.relativeResidueMap T S` is surjective. Then for every
`π : E.Carrier` with `S.ord π = 1`, every `σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier` and
every natural number `i`, the theorem proves

```lean
σ ∈ lowerRamificationGroup S F.Carrier i ↔
  σ π - π = 0 ∨ (i + 1 : ℤ) ≤ S.ord (σ π - π)
```

The proof adds no hypotheses, and the statement pair and its imports are unchanged.
The realizations `T` and `S`, the uniformizer `π` and the index `i` are arbitrary, so
`i = 0` and uniformizers other than `S.uniformizer` are included. The zero disjunct is
kept as stated. No Galois hypothesis, generation theorem or reduction to a totally
ramified subextension is used. Besides the statement, the module imports only the
published module `Langlands.ClassFieldTheory.Local.GradedUnitCoordinates`. The closing
theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Strategy

Write `O` and `m` for the integer ring `S.Integers` and its maximal ideal. Write `σ_O`
for the published restriction `integerAutomorphism S F.Carrier σ` of `σ` to `O`. By
the published `mem_lowerRamificationGroup`, which holds by `Iff.rfl`, membership of
`σ` in `lowerRamificationGroup S F.Carrier i` means `σ_O x - x ∈ m ^ (i + 1)` for every
`x : O`.

1. **Fixed residue representatives.** Every `x : O` is congruent modulo `m` to an
   element `a` with `σ_O a = a`. The surjectivity hypothesis gives a base integer whose
   image in `O` has the same residue as `x`, and every `F.Carrier`-algebra automorphism
   fixes that image.
2. **Test on one generator.** Let `ϖ : O` generate `m`. Under step 1, `σ_O x - x ∈ m ^ n`
   for all `x : O` exactly when `σ_O ϖ - ϖ ∈ m ^ n`. The proof is by induction on the
   exponent.
3. **Translation to the order.** Take `ϖ` to be the published integer
   `S.coordinateUniformizer π hπ`, whose value in `E.Carrier` is `π`. For `d : O`,
   `d ∈ m ^ n` exactly when `(d : E.Carrier) = 0` or `n ≤ S.ord d`. Applying this to
   `d = σ_O ϖ - ϖ`, whose value is `σ π - π`, with `n = i + 1` gives the statement.

## Generic lemmas over a local ring

Section `Generic` in namespace `Langlands.Ramification` works with a commutative local
ring `R`, an element `ϖ : R`, and any `f : H` for a type `H` with
`[FunLike H R R]` and `[RingHomClass H R R]`. Write `m = maximalIdeal R`. The two lemmas
take the hypotheses `hϖ : maximalIdeal R = Ideal.span {ϖ}` and

```lean
hrep : ∀ x : R, ∃ a : R, f a = a ∧ x - a ∈ maximalIdeal R
```

- `sub_mem_maximalIdeal_pow_of_fixed hϖ f hrep hf`: if `hf : f ϖ - ϖ ∈ m ^ n`, then
  `f x - x ∈ m ^ k` for every `k ≤ n` and every `x : R`. The proof is by induction on
  `k`, the case `k = 0` being trivial. For the step, `hrep` and `hϖ` write
  `x = a + b * ϖ` with `f a = a`. Then

  ```text
  f x - x = f b * (f ϖ - ϖ) + (f b - b) * ϖ.
  ```

  The first summand lies in `m ^ n ≤ m ^ (k + 1)`. By the induction hypothesis for `b`,
  the second lies in `m ^ k * m = m ^ (k + 1)`.
- `forall_sub_mem_maximalIdeal_pow_iff_of_fixed hϖ f hrep n`: the statement
  `∀ x, f x - x ∈ m ^ n` is equivalent to `f ϖ - ϖ ∈ m ^ n`. The forward direction
  evaluates at `ϖ`; the reverse direction is the previous lemma with `k = n`.

## Order and ideal powers

Section `Langlands.PadicField.TopologicalData` adds two lemmas for arbitrary
`F : PadicField.{u} p` and `T : F.TopologicalData`. Recall the published convention
`T.ord 0 = 0`.

- `mem_integers_iff_zero_le_ord T hx`: for `x ≠ 0`, `x ∈ T.Integers` exactly when
  `0 ≤ T.ord x`. The published `normalizedAbs_le_one_iff_mem_integers` and
  `normalizedAbs_of_ne_zero` rewrite integrality as
  `(T.residueCardinality : ℝ) ^ (-T.ord x) ≤ 1`. Since the residue cardinality exceeds
  one (published `residueCardinality_gt_one`), this holds exactly when
  `-T.ord x ≤ 0`.
- `mem_maximalIdeal_pow_iff_ord T π hπ n d`: for `hπ : T.ord π = 1`, `n : ℕ` and
  `d : T.Integers`,

  ```lean
  d ∈ IsLocalRing.maximalIdeal T.Integers ^ n ↔
    (d : F.Carrier) = 0 ∨ (n : ℤ) ≤ T.ord (d : F.Carrier)
  ```

  The published `mem_maximalIdeal_pow_iff_coordinate_dvd` replaces membership by
  divisibility by `T.coordinateUniformizer π hπ ^ n` in `T.Integers`, and
  `T.ord (π ^ n) = n` follows from the published `ord_zpow`. If `d = π ^ n * c` with
  `c` integral, then either `c = 0` and `d = 0`, or `T.ord d = n + T.ord c ≥ n` by
  `ord_mul` and the previous lemma. Conversely, `d = 0` is divisible by everything.
  If `d ≠ 0` and `n ≤ T.ord d`, the quotient `d / π ^ n` has order
  `T.ord d - n ≥ 0` by `ord_mul` and `ord_inv`. It is therefore integral, and it
  witnesses the divisibility.

## The Padic criterion

Section `Criterion` in namespace `Langlands.Ramification.Padic` fixes the data of the
statement.

- `exists_fixed_residue_representative T S hsurj σ x`: for every `x : S.Integers`
  there is `a : S.Integers` with `integerAutomorphism S F.Carrier σ a = a` and
  `x - a ∈ maximalIdeal S.Integers`. Surjectivity of `relativeResidueMap T S` and of
  the residue map of `T.Integers` give `b : T.Integers` such that
  `S.residue (relativeIntegerMap T S b) = S.residue x`; the published
  `relativeResidueMap_residue` holds by `rfl`. Take `a = relativeIntegerMap T S b`,
  whose value is `algebraMap F.Carrier E.Carrier b`. Then `σ` fixes it by
  `AlgEquiv.commutes`, and equal residues mean that `x - a ∈ maximalIdeal S.Integers`.
- `mem_lowerRamificationGroup_iff_uniformizer T S hsurj π hπ σ i` is the displayed
  equivalence. It rewrites with `mem_lowerRamificationGroup`, then with the generic
  equivalence for `f = integerAutomorphism S F.Carrier σ`,
  `ϖ = S.coordinateUniformizer π hπ` and the published
  `S.maximalIdeal_eq_span_coordinateUniformizer π hπ`, and then with
  `S.mem_maximalIdeal_pow_iff_ord π hπ (i + 1)`. The value of
  `integerAutomorphism S F.Carrier σ ϖ - ϖ` in `E.Carrier` is `σ π - π`, by
  `coordinateUniformizer_coe`. A cast normalization identifies `((i + 1 : ℕ) : ℤ)` with
  `(i : ℤ) + 1`.
- `uniformizerCriterion` introduces the binders of `UniformizerCriterion.{u, v}` and
  applies the previous theorem.

## Correspondence with the original source

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979 (registered source
`serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`, which I checked).
Chapter IV, §1, Lemma 1, printed p.61 (PDF p.68), fixes a Galois extension `L/K` and an
element `x` generating `A_L` as an `A_K`-algebra. It says that `s` acts trivially on
`A_L / p_L^{i+1}` exactly when `v_L(s(a) - a) ≥ i + 1` for all `a ∈ A_L`, and exactly
when `v_L(s(x) - x) ≥ i + 1`. Proposition 1, printed p.62 (PDF p.69), defines `G_i` by
these conditions. Chapter IV, §2, Proposition 5, printed p.66 (PDF p.73), uses the
uniformizer `π` chosen on printed p.65 (PDF p.72). It says that an element `s` of the
inertia group lies in `G_i` exactly when `s(π)/π ≡ 1 mod p_L^i`. Serre's proof reduces to
the totally ramified case and uses Chapter I, §6, Proposition 18: there `π` generates
`A_L` as an `A_K`-algebra. Lemma 1 then gives `i_G(s) = v_L(s(π) - π)`.

The Lean proof differs from Serre's route as follows. It does not use that `π` generates
the integer ring as an algebra over the base integers, and it assumes no Galois
hypothesis. Surjectivity of the actual relative residue map is the total-ramification
input. With it, steps 1 and 2 above replace the generation argument by fixed residue
representatives and induction on the exponent. This is the mechanism sketched in the
statement's Markdown (Worker 507, with Worker 32's formulation and derivation). The
order condition `(i + 1 : ℤ) ≤ S.ord (σ π - π)` is Serre's `v_L(s(π) - π) ≥ i + 1`. Under
the Library convention `S.ord 0 = 0`, the case `σ π = π` needs the explicit zero
disjunct, which step 3 supplies.

## Reused work

All reused results are imported by their Lean names, and none is copied or modified.
The relevant authors are as follows.

- Worker 40 authored `Langlands.LocalFactor.Ramification.Galois`. That module supplies
  `integerAutomorphism`, `lowerRamificationGroup` and `mem_lowerRamificationGroup`.
- Worker 90 authored `Langlands.LocalField.RelativeIntegers`. That module supplies
  `relativeIntegerMap`, `relativeResidueMap` and `relativeResidueMap_residue`.
- Worker 96 authored `Langlands.ClassFieldTheory.Local.GradedUnitCoordinates`, with
  Worker 27 specifying its scope. That module supplies `coordinateUniformizer`,
  `coordinateUniformizer_coe`, `coordinateUniformizer_ne_zero`,
  `maximalIdeal_eq_span_coordinateUniformizer` and
  `mem_maximalIdeal_pow_iff_coordinate_dvd`.
- Worker 27 authored the Lean proof `Langlands.LocalField.Normalization.Proof`, and
  Worker 12 reused it. That module supplies `ord_mul`, `ord_inv`, `ord_zpow`,
  `normalizedAbs_of_ne_zero`, `normalizedAbs_le_one_iff_mem_integers` and
  `residueCardinality_gt_one`.
- Worker 507 authored the target statement, with Worker 32's formulation and
  derivation.

The Lean code in this module was written by Worker 231. It was compiled with
`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Independent review, the Lake build and the exact-target check are still required for
acceptance and publication.
