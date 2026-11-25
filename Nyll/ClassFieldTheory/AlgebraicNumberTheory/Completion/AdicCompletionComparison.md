# Completion maps at finite places: comparison, finiteness, ramification

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension of number fields, w a finite place of K, and W a finite place of L above w. The library obtains a map K_w → L_W of Mathlib's adic completions in two ways. One comes from an extension of the w-adic absolute value to L and the completion of that absolute value. The other is the canonical completion of the embedding K → L. This file shows that the two agree. It then proves that L_W is finite over K_w and that valuations are raised to the ramification index.

## Definitions and results

- `finitePlaceExtensionAdicCompletionMap K L w a`: for an extension a of the w-adic absolute value to L, the ring homomorphism from `w.adicCompletion K` to the adic completion of L at the centre of a. It passes through the absolute-value completions. `..._coe` says it restricts to K → L on K, and `..._continuous` says it is continuous.
- `finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap`: it equals the canonical map `finitePlaceAdicCompletionMap K L w W`, where W corresponds to a under `finitePlaceExtensionEquivAbove`.
- `finitePlaceAdicCompletionMap_moduleFinite`: if L/K is finite, then L_W is a finite module over K_w for the canonical map.
- `finitePlaceExtensionAdicCompletionMap_norm`: ‖f(x)‖ = ‖x‖^c, where c = `finitePlaceExtensionExponent w a` is the library's positive real exponent attached to a.
- `finitePlaceAdicCompletionMap_norm_le_one_iff`: the canonical map sends x into the unit ball exactly when ‖x‖ ≤ 1.
- `finitePlaceExtensionAdicCompletionMap_valued` and `finitePlaceAdicCompletionMap_valued`: v_W(f(x)) = v_w(x)^e for every x ∈ K_w, where e is the ramification index `ramificationIdx'` of W over w.

## Proofs

The two maps agree on the dense image of K and are continuous, so they are equal. Finiteness is transported from `completionModuleFinite` for absolute-value completions. For the valuation formula, a nonzero x is written as z·k with k ∈ K and v(z) = 1. The norm formula gives v(f(z)) = 1, and for k ∈ K the formula is Mathlib's `HeightOneSpectrum.valuation_liesOver`.

## Points to watch

- The exponent `finitePlaceExtensionExponent` and the map `finitePlaceExtensionEquivAbove` between extensions of absolute values and places of L are the library's own, defined in imported files.
- The ramification index appears through the variant `ramificationIdx'`. It is converted to Mathlib's `ramificationIdx` inside the proof.
- Only the finiteness statement assumes L/K finite.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/AdicCompletionComparison.lean`: the Lean file is the source byte for byte (SHA-256 `61064acb8d31186afa5a00f2b1516f4388919d126366795f654369376164b93c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
