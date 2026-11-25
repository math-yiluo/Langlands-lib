# Unique extension of a complete absolute value to algebraic extensions

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nontrivial real-valued absolute value on a field `K` that is complete for `v`, and let `L/K` be algebraic. The file shows that `v` has exactly one extension to `L`. Both the archimedean and the nonarchimedean case are covered.

## Main definitions and results

- `UniqueExtension v`: a structure holding an absolute value on `L`, a proof that it extends `v` in the sense of `Extends`, and a proof that every extension of `v` equals it.
- `uniqueAlgebraicExtension v hcomplete hv`: such a structure, for `L/K` algebraic, `WithAbs v` complete and `v` nontrivial.
- `existsUnique_extends_of_isAlgebraic`: the same fact as a unique-existence statement `∃! w, Extends v w`.
- `algebraicExtension_nonarchimedean`: the nonarchimedean case, whose extension is the spectral extension `spectralExtension` of the imported file. Uniqueness there is `eq_spectralExtension_of_extends`.
- `algebraicExtension_archimedean`: the archimedean case. It does not need nontriviality.

## Auxiliary constructions

- `rpow v s`: the power `v^s` for `0 < s ≤ 1`. `nonarchimedeanRpow` is the power for any `s > 0` when `v` is nonarchimedean, and `isEquiv_nonarchimedeanRpow` says that it is equivalent to `v`.
- `compAlgEquiv e w`: the pullback of an absolute value along a `K`-algebra isomorphism. It preserves `Extends` (`compAlgEquiv_extends`) and completeness (`compAlgEquiv_complete`).
- `algebraicExtension_realRpow` and `algebraicExtension_complexRpow`: for `L` algebraic over `ℝ` or over `ℂ`, the absolute value `|·|^s` with `0 < s ≤ 1` extends uniquely. The proof uses that `L` is isomorphic to `ℝ` or `ℂ`.
- `algebraicExtension_baseRingEquiv`: transports a unique extension along a ring isomorphism of the base field. The companion lemma `algebraicExtension_isAlgebraic_of_base_ringEquiv` transports algebraicity.

## Proof

In the archimedean case, Ostrowski's theorem for complete fields (`ostrowski_of_complete`, imported) gives a ring isomorphism of `K` with `ℝ` or `ℂ` under which `v` becomes `|·|^s` with `0 < s ≤ 1`. The extension is then transported from the real or complex case. The nonarchimedean case rests entirely on the spectral norm construction of the imported file.

## Points to watch

- "Extension" means exact equality of values (`Extends`), not equivalence of absolute values.
- Completeness is an explicit hypothesis `CompleteSpace (WithAbs v)`, not an instance. Absolute values take values in `ℝ`.
- All these constructions are `noncomputable`. The archimedean ones (`algebraicExtension_realRpow`, `algebraicExtension_archimedean`) are obtained with `Classical.choice`; the nonarchimedean one takes `spectralExtension` directly.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/Core.lean`: the Lean file is the source byte for byte (SHA-256 `71e0b44b6744706d3366bb0784dc992999d12881f7d93f6297ac5d9bc74ad320`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
