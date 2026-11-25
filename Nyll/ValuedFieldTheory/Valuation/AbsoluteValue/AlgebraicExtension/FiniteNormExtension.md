# Norm formula for the extension of a complete absolute value to a finite extension

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nontrivial real-valued absolute value on a field `K`, complete for `v`, and let `L/K` be finite. The file shows that the unique extension of `v` to `L` is `x ↦ v(N(x))^(1/[L:K])`, with `N` the field norm from `L` to `K`, and that `L` is complete for it. Both the archimedean and the nonarchimedean case are covered.

## Main definitions and results

- `FiniteNormExtensionFiniteExtensionResult v`: a structure packaging an absolute value on `L` with four properties. It restricts to `v` on `K` and every other such absolute value equals it. Its value at `x` is `finiteExtensionNormFormulaValue v x`, that is `v(N(x))^(1/[L:K])`, and `L` is complete for it. `ext_unique` says that two such packages are equal.
- `finiteNormExtension_finite_extension`: such a package, for `v` complete (`IsCompleteForAbsoluteValue v`) and nontrivial.
- `finiteNormExtension_nonarchimedean_finite_extension` and `finiteNormExtension_archimedean_finite_extension`: the two cases. The archimedean one does not use nontriviality.
- `finiteNormExtension_finite_normFormulaAbsoluteValue`: in the nonarchimedean case, the norm formula bundled as an absolute value on `L`. Its properties are separate theorems:
  - `_apply`: its values;
  - `_extends_base`: it restricts to `v`;
  - `_complete`: `L` is complete for it;
  - `finiteNormExtension_finite_normFormulaValue_strong_triangle`: the ultrametric inequality;
  - `finiteNormExtension_unique_extension_finite_normFormulaAbsoluteValue`: every extension of `v` equals it.

## Proofs

In the nonarchimedean case, the norm formula is compared with Mathlib's spectral norm. The spectral norm of `x` is `v(a₀)^(1/d)`, where `a₀` is the constant coefficient and `d` the degree of the minimal polynomial of `x`. Also `N(x) = ±a₀^[L:K(x)]`. So the formula agrees with the spectral extension of the imported file, which gives multiplicativity, the ultrametric inequality, completeness and uniqueness.

In the archimedean case, Ostrowski's theorem for complete fields (`ostrowski_of_complete`) identifies `K` with `ℝ` or `ℂ` and `v` with `|·|^s`, where `0 < s ≤ 1`. The cases `ℝ/ℝ`, `ℂ/ℝ` and `ℂ/ℂ` are computed directly; for instance `|N(z)|^(1/2) = |z|` for the norm `N` from `ℂ` to `ℝ`. Private lemmas then transport the result along the isomorphism of base fields, keeping the norm formula and completeness.

## Points to watch

- "Nonarchimedean" and "archimedean" are the library's predicates `LubinTate.Valuations.NonarchimedeanAbsoluteValue` and `ArchimedeanAbsoluteValue`. The general theorem passes the negation of the first as the second.
- Completeness is the library's predicate `IsCompleteForAbsoluteValue`. It is converted to `CompleteSpace (WithAbs v)` when needed.
- An extension must restrict exactly to `v` on `K`. Equivalence of absolute values is not enough.
- The archimedean packages are chosen with `Classical.choice`. By `ext_unique` this does not affect their value.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/FiniteNormExtension.lean`: the Lean file is the source byte for byte (SHA-256 `c94370d694b8c6b2203201ef48d60e60962e59ede3e3bf773589ac17bb09f6f6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
