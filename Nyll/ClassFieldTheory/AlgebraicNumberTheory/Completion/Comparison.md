# Comparing completions of L at an extension of a finite place

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension of number fields, v a finite place of K, and w an absolute value on L extending the v-adic absolute value `adicAbv K v` exactly. Its centre W = `finitePlaceExtensionCentre v w` is a finite place of L. This file shows that w and the standard W-adic absolute value `adicAbv L W` are equivalent, so one is a positive real power of the other. It then identifies the completion of L at w with Mathlib's adic completion `W.adicCompletion L`, and shows that the valuation rings correspond.

## Results

- `finitePlaceExtension_adicAbv_valuationSubring`: the valuation subring of `adicAbv L W` equals the valuation subring attached to w (`finitePlaceExtensionValuationSubring`).
- `finitePlaceExtension_isEquiv_adicAbv`: w and `adicAbv L W` are equivalent absolute values.
- `finitePlaceExtensionExponent v w`: a real number c, chosen so that `adicAbv L W` (x) = w(x)^c for all x ∈ L (`finitePlaceExtension_adicAbv_eq_rpow`). `finitePlaceExtensionExponent_pos` says that c > 0.
- `finitePlaceExtensionWithAbsRingEquiv`: the identity of L, viewed as a ring isomorphism between the two normed copies of L. It is continuous in both directions.
- `finitePlaceExtensionCompletionRingEquiv`: the induced ring isomorphism between the completions of L at w and at `adicAbv L W`. It is the identity on L (`..._toCompletion`) and continuous, and ‖e(x)‖ = ‖x‖^c (`..._norm`).
- `relativeFinitePlaceCompletionRingEquiv_norm`: the comparison from the absolute-value completion at W to `W.adicCompletion L` preserves norms.
- `finitePlaceExtensionAdicCompletionRingEquiv`: the composite ring isomorphism from the completion at w to `W.adicCompletion L`. It satisfies ‖f(x)‖ = ‖x‖^c, and on L it is `FinitePlace.embedding W`.
- `finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff`: f(x) lies in `W.adicCompletionIntegers L` iff x lies in the valuation ring of the completion at w.

## Proofs

Equality of the valuation subrings gives the equivalence of the absolute values: for x ≠ 0, the condition |x| < 1 is read off from x⁻¹ and the subrings. Mathlib's characterization of equivalent absolute values then supplies the exponent and continuity. The norm formula on completions holds on L and passes to the completion by density. The statement on valuation rings follows because t ↦ t^c preserves the condition t ≤ 1.

## Points to watch

- c is obtained by choice from the equivalence. The file does not express it through ramification or local degree.
- The comparison is a ring isomorphism. The file does not show it to be an isometry: norms are raised to the power c.
- Only the absolute-value extensions of v to L are used. L/K is assumed finite in the ambient variables, but most statements do not use it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/Comparison.lean`: the Lean file is the source byte for byte (SHA-256 `4922b5cb2a251403f6129039edbbc069f6b951722235c9b5e45fd605279a7c34`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
