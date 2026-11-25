# Completeness for an absolute value and the norm-formula candidate

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file sets up two basic notions for real-valued absolute values on fields: completeness, and the candidate formula for extending an absolute value to a finite extension.

- `IsCompleteForAbsoluteValue v`: `K` is complete for the uniform structure defined by `v`. This is the library's own predicate.
- `absoluteValueCompleteness_completeSpace_withAbs_iff_complete`: it is equivalent to `CompleteSpace (WithAbs v)`. One direction is `completeSpace_withAbs_of_isCompleteForAbsoluteValue`. The proof rests on `absoluteValue_uniformSpace_eq_toNormedField`: the uniformity of `v` is that of the induced normed field.
- `absoluteValueCompleteness_complete_iff_cauchySeq_converges`: completeness holds exactly when every Cauchy sequence converges.
- `withAbsNontriviallyNormedField v hv`: for nontrivial `v`, a `NontriviallyNormedField` structure on `WithAbs v`. It is a definition, not a global instance.
- `finiteExtensionNormFormulaValue v x`: for `L/K` finite, the real number `v(N(x))^(1/[L:K])`, with `N` the field norm from `L` to `K`. `finiteExtensionNormFormulaValue_nonneg` says that it is nonnegative.

The norm-formula value is only a function here. The file does not claim that it is an absolute value.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Completeness.lean`: the Lean file is the source byte for byte (SHA-256 `2761db767e7e3ee5f1aa96ebf5ca3ead0b929182e0084884d5546559cc18cdb4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
