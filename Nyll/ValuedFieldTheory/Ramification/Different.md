# The different of a finite extension of complete discretely valued fields

Module `Nyll.ValuedFieldTheory.Ramification.Different`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite extension of complete discretely valued fields (`CompleteDVF`), with valuation rings `𝒪_K ⊆ 𝒪_L`. The file specializes Mathlib's different ideal `differentIdeal` and the trace dual to this situation: different and codifferent, the unramifiedness criterion, the formula for a monogenic extension, Dedekind's lower bound in terms of the ramification index, and the tower formula. The ideal itself is Mathlib's; most results restate Mathlib theorems after supplying their hypotheses.

## Main definitions

- `codifferentSubmodule base target`: the trace dual of `𝒪_L`, as an `𝒪_L`-submodule of `L`.
- `differentIdealOfFiniteSeparable base target`: Mathlib's `differentIdeal 𝒪_K 𝒪_L`, built with the torsion-freeness that holds when `L / K` is separable; `differentIdealOfFiniteSeparable_eq_differentIdeal` identifies it with `differentIdeal` whenever such an instance is present.

## Main results

Most results come in two forms: one for `differentIdeal` with module-finiteness, torsion-freeness and separability of fraction fields as instance hypotheses (and, for the codifferent and monogenic results, `IsIntegralClosure 𝒪_L 𝒪_K L`), and one, with `OfFiniteSeparable` or `_of_finite_separable` in its name, that derives these from separability of `L / K` but still takes the instance `IsScalarTower 𝒪_K 𝒪_L L`.

- Codifferent: `z` is in it iff `Tr(z a)` is integral over `𝒪_K` for every `a ∈ 𝒪_L` (`mem_codifferentSubmodule_iff_trace_mul_integral…`); `D = 1 / codifferent` (`coeSubmodule_differentIdeal…_eq_one_div_codifferent`); multiplying by the discriminant of a `K`-basis of `L` made of integral elements makes codifferent elements integral (`isIntegral_discriminant_mul_of_mem_codifferent…`).
- `differentIdeal_ne_bot`, `differentIdealOfFiniteSeparable_ne_bot`: the different is nonzero.
- Unramifiedness: `𝔪_L ∤ D` iff `D` is a unit iff `D = ⊤` iff `Algebra.IsUnramifiedAt 𝒪_K 𝔪_L` (`maximalIdeal_not_dvd_…_iff_isUnramifiedAt`, `isUnit_…`, `…_eq_top_iff_isUnramifiedAt`).
- Monogenic case: if `z ∈ 𝒪_L` generates `L` over `K`, then `conductor · D = (f′(z))` for `f` the minimal polynomial of `z` over `𝒪_K`, and `f′(z) ∈ D`. `isUnramifiedAt_of_aeval_derivative_isUnit`: if some `P` over `𝒪_K` has `P(z) = 0` and `P′(z)` a unit, the extension is unramified at `𝔪_L`.
- Dedekind's bound: if `𝔪_L^e` divides `𝔪_K 𝒪_L` then `𝔪_L^(e − 1)` divides `D`; in particular for `e` the ramification index. Consequently `e > 1` forces `𝔪_L ∣ D`, and then the extension is not unramified at `𝔪_L` (`not_isUnramifiedAt_of_one_lt_ramificationIndex_of_finite_separable`).
- `differentIdeal_tower`, `differentIdealOfFiniteSeparable_tower`: `D(L/K) = D(L/M) · D(M/K) 𝒪_L` for a tower `K ⊆ M ⊆ L`.

## Watch for

- "Unramified" here is Mathlib's `Algebra.IsUnramifiedAt`, not the library's `IsFiniteUnramified`; the file does not relate the two.
- Only a lower bound for the different is proved: `𝔪_L^(e − 1) ∣ D`, not the exact exponent, nor the distinction between tame and wild ramification. Likewise `e > 1` implies ramified, but the converse is not stated.
- The algebra structure between fraction rings is a local instance (`FractionRing.liftAlgebra`), turned on for this file only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Different.lean`: the Lean file is the source byte for byte (SHA-256 `bfc04da61dbf1b332b6d7e2e6f022ac270f4931caa1b10f56b4c5d18cf09f357`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
