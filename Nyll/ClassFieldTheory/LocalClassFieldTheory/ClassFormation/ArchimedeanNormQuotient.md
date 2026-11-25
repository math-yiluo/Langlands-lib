# The local class-formation axiom at infinite places

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields, `v` an infinite place of `K` and `w` an infinite place of `L` above it. This file computes the Herbrand groups of the decomposition group of `w` acting on the units of the local extension at `w`: `H⁻¹` is trivial, when `Gal(L/K)` is cyclic with a given generator, and `H⁰` has order equal to the local degree, one if `w` is unramified and two if `w` is complex over a real `v`. The key computation is that the norms from `ℂˣ` are the positive reals, so the sign identifies `ℝˣ / N(ℂˣ)` with `ℤˣ`.

## Main definitions and results

- `infinitePlaceAbsoluteValueExtension v w hw`: `w` as an extension of the absolute value `v`, the format used by the library's local completion `LocalizedCompletion`.
- `absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer`: for an infinite place, the library's decomposition group is the stabilizer of `w` in `Gal(L/K)`.
- `normQuotientEquivOfRingEquiv`: the norm quotient `Kˣ / N(Lˣ)` is invariant under compatible ring isomorphisms of base and extension. It is used to identify the local norm quotients with `NormQuotient ℝ ℂ` (`infiniteCompletionNormQuotientEquivRealComplex`, `localizedCompletionNormQuotientEquivAbsoluteCompletions`, `absoluteCompletionNormQuotientEquivRealComplex`).
- `realUnitsSign : ℝˣ →* ℤˣ`: the sign, surjective and continuous; its kernel is the positive reals, which is `localNormSubgroup ℝ ℂ` (`realUnitsSign_ker_eq_complexNormSubgroup`).
- `realComplexNormQuotientEquivSign : NormQuotient ℝ ℂ ≃* ℤˣ`; hence `realComplexNormQuotient_card_eq_two`.
- `herbrandH0_card_eq_one_of_group_card_eq_one`: a trivial group has trivial `H⁰`.
- `infinitePlaceLocalHerbrandH0_card_eq_localDegree`: `|H⁰(D_w, L_wˣ)| = 1` if `w` is unramified over `K`, else `2`.
- `infinitePlaceLocalClassAxiom_cards`: for `σ` a generator of a cyclic `Gal(L/K)`, `|H⁻¹| = 1` and the same formula for `|H⁰|`.
- `infinitePlaceLocalHerbrandH0Finite`, `infinitePlaceLocalHerbrandHMinusOneFinite`: both groups are finite.

## Proofs

At an unramified place the stabilizer has one element (Mathlib's `InfinitePlace.card_stabilizer`), so `H⁰` is trivial. At a ramified place `v` is real and `w` complex; the library's `localHerbrandH0EquivNormQuotient` identifies `H⁰` with the local norm quotient, which is transported to `ℝˣ / N(ℂˣ)`, of order two. The `H⁻¹` statement is the Hilbert 90 result of the file `ArchimedeanHilbert90`.

## Remarks

- In the theorems on Herbrand groups, `K` and `L` live in `Type`, and the `H⁻¹` statement needs `Gal(L/K)` cyclic with a chosen generator `σ`.
- The local structures (completion algebras, Galois property, the action of the decomposition group on local units) are bound with `let` inside the statements.
- `NormQuotient`, `HerbrandH0` and `HerbrandHMinusOne` are the library's own definitions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ArchimedeanNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `c60d31fe0410f236d01b7891408406cdb02c99f7412659cb57909b1a97cdae34`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
