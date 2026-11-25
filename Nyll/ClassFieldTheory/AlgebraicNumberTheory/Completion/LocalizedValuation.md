# Valuation rings of completions and of their algebraic localizations

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let vK be a nonarchimedean absolute value on K, L/K a finite extension, and w an absolute value on L extending vK exactly (`AbsoluteValueExtension vK L`). The library attaches to w an algebraic localization `LocalizedCompletion vK w`, a finite extension of the completion of K at vK. This file puts on the completion and on this localization the valuations induced by their norms, and shows that the valuation ring of the localization is the integral closure of the valuation ring of the completed base.

## Definitions and results

- `finitePlaceCompletionValued`, `finitePlaceCompletionValuativeRel`: the ℝ≥0-valued valuation x ↦ ‖x‖ on the completion of K at vK and its valuation relation; `completionIsUltrametricDist` provides the ultrametric distance they need.
- `localizedCompletionFinitePlaceValued`, `localizedCompletionFinitePlaceValuativeRel`, `localizedCompletionIsUltrametricDist`: the same on `LocalizedCompletion vK w`.
- `finitePlaceCompletion_mem_integers_iff_norm_le_one`, `localizedCompletion_mem_integers_iff_norm_le_one`: an element lies in the valuation ring exactly when its norm is at most 1.
- `localizedCompletion_integerRing_eq_integralClosure`: for vK nontrivial, the valuation ring of the localization equals the integral closure in it of the valuation ring of the completion of K. `localizedCompletionIsIntegralClosure` restates this as `IsIntegralClosure`.
- `localizedCompletionValuationHasExtension`: the two norm valuations form a `Valuation.HasExtension` pair.
- `localizedCompletionIsIntegralClosureWithExtension`: the integral-closure statement again, with the algebra structure on valuation rings that this extension pair uses.

## Proof

Both valuation rings are identified with the valuation subrings of the corresponding absolute values, through the library's exponential valuations. The completion of K is complete, hence Henselian (`henselianValuation_of_complete`). Over a Henselian base, the valuation ring of a finite extension with an extending valuation is the integral closure (`exponentialValuationSubring_eq_integralClosure_of_henselian`). Finiteness comes from `localizedCompletionModuleFinite`.

## Points to watch

- The valued structures are reducible definitions, not instances: each statement installs them with local `let` bindings, and its conclusion refers to those choices.
- Nonarchimedeanness of vK is an explicit hypothesis, and nontriviality is needed for the integral-closure results. vK is any such absolute value on K, not necessarily one of the normalized absolute values of finite places.
- `LocalizedCompletion` is the library's own construction.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/LocalizedValuation.lean`: the Lean file is the source byte for byte (SHA-256 `b83fddfb9ba11b0b4b5c5d8d4efa99136186cef3566b557aa33e5624238ff838`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
