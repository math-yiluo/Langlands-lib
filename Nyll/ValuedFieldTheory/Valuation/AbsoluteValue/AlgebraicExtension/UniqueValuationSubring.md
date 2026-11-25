# The extension valuation ring is the integral closure

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `V` be a valuation subring of a field `K` and `L/K` an extension such that every `z ∈ L` or its inverse is integral over `V`. Then every valuation on `L` extending that of `V` has the integral closure of `V` as its valuation ring.

- `DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv`: under this hypothesis, let `wL` be a valuation on `L` with values in any linearly ordered commutative group with zero, extending the valuation of `V` (Mathlib's `Valuation.HasExtension`). Its valuation subring equals `integralClosureValuationSubringOfMemOrInv`, the integral closure made into a valuation subring.

Proof: the integral closure `B` lies in the valuation ring of `wL`. The ideal of `B` cut out by that ring contracts to the maximal ideal of `V`. By integrality it is maximal in `B`, so the valuation ring of `wL` equals `B`.

No finiteness, separability, discreteness or completeness is assumed. The dichotomy hypothesis `hval` carries the content; the henselian norm-formula results supply it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/UniqueValuationSubring.lean`: the Lean file is the source byte for byte (SHA-256 `26a5868c0b8a6be5979e1466aeeb5184c1a28c93d2e3f32979a9185e2e515e0f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
