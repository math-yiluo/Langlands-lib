# Prime norms from conjugate Frobenius fixed fields

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.ConjugatePrimeNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A step in the proof that the abstract reciprocity map is multiplicative, for a compact Hausdorff topological group `G`, a `G`-module `A`, a degree map `D` and valuation data `v`. For a finite abstract field `K`, a finite Galois extension `L | K`, Frobenius elements `φ`, `σ` and `m ∈ ℕ`, an earlier file defines a conjugate Frobenius element `σ' = frobeniusActionConjugate φ σ m` whose fixed field `Σ'` is the conjugate of the fixed field `Σ` of `σ` by a representative of `φ^m`. This file shows that `Σ'` has a prime element with the same norm to `K` as a given prime element of `Σ`.

## Main result

- `DegreeData.exists_primeElement_frobeniusActionConjugate_norm_eq`: if `π` is a prime element of `Σ` (normalized valuation one), there is a prime element `π'` of `Σ'` with `N(Σ'|K)(π') = N(Σ|K)(π)` in `A_K`.

## Proof

Take `π'` to be the conjugate of `π` by the representative `k ∈ G_K` of `φ^m`, viewed in `A_Σ'`. Primality is kept because the normalized valuation is compatible with conjugation. The norm from the conjugate field is the conjugate of the norm, and conjugating by `k` does nothing on `A_K` since `k ∈ G_K`; the conjugate of `G_K` by `k` is `G_K` itself.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/ConjugatePrimeNorm.lean`: the Lean file is the source byte for byte (SHA-256 `ffec7244b45a0f7db3da9b44159e90e88b30da0b28358a9e3c7703890027de79`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
