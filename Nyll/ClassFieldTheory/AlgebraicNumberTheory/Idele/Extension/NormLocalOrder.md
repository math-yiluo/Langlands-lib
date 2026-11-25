# Local orders of norms at finite places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite extension of number fields, `v` a finite place of `K`, and `W` a finite place of `L` above `v`. The file proves that the local norm `L_Wˣ → K_vˣ` multiplies orders by the inertia degree: `ord_v(N x) = f(W | v) · ord_W(x)`.

## Main result

- `FiniteIdeleGroup.localOrder_normUnits`: for `x ∈ L_Wˣ`, `localOrder v (normUnits K_v L_W x) = inertiaDeg(W | v) · localOrder W x`. Here `L_W` is made a `K_v`-algebra by the completion map `finitePlaceAdicCompletionMap`, and `normUnits` is the library's norm on unit groups.

## Proof

Inside the proof, both completions are given the structure of nonarchimedean local fields from their `ℤᵐ⁰`-valued valuations. The valuation of `K_v` extends to `L_W` because the completion map raises valuations to the power of the ramification index. The library's norm–valuation theorem for finite separable extensions of local fields (`LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable`) then gives `v(N x) = [k_W : k_v] · v(x)` for the intrinsic valuations. Private lemmas and definitions transfer this to the problem at hand:

- `normalizedValue_eq_withZeroLog_of_surjective`: a surjective `ℤᵐ⁰`-valuation compatible with the valuative relation gives the same normalized value as the intrinsic valuation of a local field.
- `intrinsicIntegerEquivValuedInteger`, `intrinsicResidueFieldEquivValuedResidueField`: the corresponding valuation rings and residue fields agree.
- `absNorm_eq_card_intrinsicAdicResidueField`: the absolute norm of `v` is the size of the residue field of `K_v`. Comparing `|k_W| = |k_v|^f` then identifies the residue degree with Mathlib's `inertiaDeg`.

## Points to watch

- The `K_v`-algebra structure on `L_W` is fixed by `let` in the statement, and the local-field structures are built only inside the proof, not as global instances.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/NormLocalOrder.lean`: the Lean file is the source byte for byte (SHA-256 `107a616ce757739c8b1664cb58b2e1eaf16baac2f7d9d4c1aac2bed42a212775`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
