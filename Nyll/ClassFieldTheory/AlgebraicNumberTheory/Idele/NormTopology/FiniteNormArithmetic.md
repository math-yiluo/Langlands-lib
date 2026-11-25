# Finite-place arithmetic of idele norms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.FiniteNormArithmetic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. At the finite places, this file computes how the idele norm I_L → I_K and the extension map I_K → I_L interact with local orders and with the finite part of the absolute idele norm, ∏_v N(p_v)^(ord_v).

## Main results

- `IdeleGroup.primeNorm_above`: for a finite place W of L over v of K, the absolute norm of the prime of W is N(p_v)^f, where f is the inertia degree of W over v.
- `IdeleGroup.finiteComponentOrder_norm`: for an idele a of L, the order at v of the v-component of `norm K L a` is the sum over the places W above v of f(W | v) · ord_W(a_W).
- `IdeleGroup.finiteAbsoluteNorm_norm`: the finite absolute norm of `norm K L a` equals the finite absolute norm of a.
- `IdeleGroup.fractionalIdealAbsoluteNorm_extension_prime`: the extension to L of the prime p_v, as a fractional ideal, has absolute norm N(p_v)^[L : K].
- `IdeleGroup.finiteAbsoluteNorm_extension`: for an idele a of K, the finite absolute norm of `extension K L a` is that of a raised to the power [L : K].

Private helpers write the finite absolute norm as a product over all finite places, regroup such products over the fibres of the map from places of L to places of K, and extend the prime case to every nonzero fractional ideal.

## Proof

The order formula applies the imported `FiniteIdeleGroup.localOrder_normUnits` to each factor of `finiteComponent_norm_eq_prod`. Invariance under the norm then follows by writing N(p_v)^(f·n) = N(p_W)^n and regrouping over fibres.

The extension formula moves to fractional ideals through `absoluteNorm_eq_fractionalIdealAbsoluteNorm` and `fractionalIdeal_extension`. It proves the prime case from Mathlib's `Ideal.absNorm_algebraMap` and extends it by unique factorization (`FractionalIdealGroup.factorization_surjective`).

## Points to watch

- `FiniteIdeleGroup.absoluteNorm`, `FiniteIdeleGroup.localOrder`, `FractionalIdealGroup` and its `absoluteNorm` and `extension` are the library's own definitions. The two absolute norms take values in ℝ≥0ˣ. The finite absolute norm is ∏_v N(p_v)^(ord_v), the reciprocal of the usual ∏_v |a_v|_v at the finite places.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormTopology/FiniteNormArithmetic.lean`: the Lean file is the source byte for byte (SHA-256 `7ed28bc26c5d7592208693834ffd02438f9055079b4816f716d3eca537308e4b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
