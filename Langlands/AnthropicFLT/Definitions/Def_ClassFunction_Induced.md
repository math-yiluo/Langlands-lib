# `Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced`

Ported by Worker 84 for the exact-target proof of
`Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement` (Brauer's induction theorem, an input of
Henniart's 2000 proof; program `34b81620-20d7-4059-9b08-6bedd1c1c029`). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_ClassFunction_Induced.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

The source closure was audited in the Library note `notes/reuse/anthropic-brauer-audit.md` (task `6f660c3b-fd16-4067-8f6a-611939522624`, Worker 18).

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text. (The audit's compatibility edit 1, an extra `rfl` in `induced_conj`, is not needed under the lakefile options and is not applied.)

## Content

Normalized induction of functions from a subgroup (namespace `ClassFunction`), for a finite group `G` and a field `K`.

- `induced H φ g = (Nat.card H)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0`, for a subgroup `H` and any function `φ : G → K` (defined with classical decidability; `induced_apply` restates it for any decidable membership instance). The input need not be a class function, and only its values on `H` matter (`induced_congr`). This is an operation on functions: it neither constructs an induced representation nor proves a character formula.
- `induced_conj`: the result is invariant under conjugation `g ↦ y⁻¹ * g * y`.
- Linearity: `induced_add`, `induced_zero`, `induced_const_mul`, `induced_sum` (finite sums).
- `induced_mul_of_conj_invariant`: for a conjugation-invariant `f`, `induced H φ g * f g = induced H (φ * f) g`.
- In characteristic zero: `induced_top_of_conj_invariant` (inducing a conjugation-invariant function from `⊤` returns it), and `induced_induced` (induction in stages: inducing from `H` the extension by zero of `induced L ψ`, for `L` a subgroup of `H`, equals inducing from the image `L.map H.subtype` the extension by zero of `ψ`).

## Declarations

Names, namespaces and statements are the FLT ones.

- def `ClassFunction.induced`
- theorem `ClassFunction.induced_apply`
- theorem `ClassFunction.induced_congr`
- theorem `ClassFunction.induced_conj`
- theorem `ClassFunction.induced_add`
- theorem `ClassFunction.induced_zero`
- theorem `ClassFunction.induced_const_mul`
- theorem `ClassFunction.induced_sum`
- theorem `ClassFunction.induced_mul_of_conj_invariant`
- theorem `ClassFunction.induced_top_of_conj_invariant`
- theorem `ClassFunction.induced_induced`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
