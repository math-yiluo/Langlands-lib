# Finite and algebraic unramified extensions of valued fields

Module `Nyll.ValuedFieldTheory.LocalField.Unramified.Definitions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines unramified extensions in two settings, each with a finite and an algebraic version: for discretely valued fields bundled as `DVF` / `CompleteDVF`, and for exponential valuations `w : L → ℝ ∪ {∞}` (`ExponentialValuation`) extending `v` on `K`. A finite extension is unramified when the residue extension is separable and `[L : K]` equals the residue degree; an algebraic one is unramified when it is covered by finite unramified subextensions.

## Discretely valued fields

- `ValuedExtension.IsFiniteUnramified base target`: for `L / K` finite, residue extension separable and `degree = residueDegree`.
- `isFiniteUnramified_iff_residueSeparable_and_hasRamificationIndexOne`: for complete discretely valued `K`, `L` with `L / K` finite and separable, this is equivalent to residue separability plus ramification index one, using the equality `e = 1 ⇔ f = [L : K]` proved elsewhere.
- `IsFiniteUnramifiedSubextension base ambient E`: `E / K` is finite and separable and carries some complete discrete valuation, compatible with those of `K` and `L`, for which it is finite unramified.
- `IsAlgebraicUnramifiedExtension`: every finite subset of `L` lies in one such `E`; `exists_isFiniteUnramifiedSubextension_of_fg` extends this to finitely generated intermediate fields.

## Exponential valuations

Here `hExt` says `w` restricts to `v`.

- `exponentialValuationRestrict`: restriction of `w` to an intermediate field.
- `unramifiedValuationRingValuationRingMap`: the induced local map of valuation rings, hence of residue fields; `ResidueExtensionIsSeparable`: separability of that residue extension.
- `FiniteUnramifiedExtension`: residue separability and `[L : K] = exponentialResidueDegree v w hExt`; two projection lemmas.
- `FiniteUnramifiedSubextension`, `finiteUnramifiedSubextensionUnion`: finite intermediate fields that are unramified for the restricted valuation, and their union.
- `AlgebraicUnramifiedExtension`: for `L / K` algebraic, that union is all of `L`; `algebraicUnramifiedExtension_iff` restates it elementwise.
- `AlgebraicUnramifiedExtensionFiniteSupport`: every finite subset lies in one finite unramified subextension; `algebraicUnramifiedExtension_of_finiteSupport` proves it implies the union form.

## Watch for

- `IsFiniteUnramified` is not `HasRamificationIndexOne` (the docstring calls the latter the historical `IsUnramified`): it demands residue separability and the degree equality, and does not ask `L / K` to be separable. Under the hypotheses of the equivalence above, it amounts to `HasRamificationIndexOne` together with residue separability, not to `HasRamificationIndexOne` alone.
- In the discrete setting the algebraic notion is defined directly in the finite-support form, which is a priori stronger than "union of finite unramified subextensions". In the exponential setting the literal union is the definition, and only finite support ⇒ union is proved; the converse, which needs closure under compositum, is not in this file.
- `IsFiniteUnramifiedSubextension` asks `E / K` to be separable; `FiniteUnramifiedSubextension` does not.
- Both are the library's own definitions, not Mathlib's `Algebra.Unramified`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Unramified/Definitions.lean`: the Lean file is the source byte for byte (SHA-256 `8ed0af76ee50185392d21f821a34c5e75f37b67b0d88d440ac365729a203128d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
