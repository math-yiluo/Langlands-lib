# Complete nonarchimedean absolute values are Henselian

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Complete`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` with a real-valued absolute value `v` that is nonarchimedean and complete, the file shows that its valuation ring satisfies the library's factorization form of Hensel's lemma.

- `henselFactorization_of_complete`: the valuation subring `absoluteValueValuationSubring v` has `HenselFactorizationProperty`. Concretely, for a polynomial `f` over it whose reduction is nonzero and factors as a coprime product `ḡ · h̄`, there are `G`, `H` with `f = G · H`, reducing to `ḡ` and `h̄`, with `deg G = deg ḡ` and `deg H ≤ deg f − deg ḡ`.
- `henselianValuation_of_complete`: the associated valuation is `HenselianValuationByFactorization`.

The factorization itself is `henselFactorization_complete_exists_factorization`, proved in an imported file; this file adds the nonvanishing of the factors and the degree bound, and passes to the second notion through `henselianValuation_iff_henselFactorization`.

## Caveats

- `HenselFactorizationProperty` and `HenselianValuationByFactorization` are the library's own notions of Henselianity, not Mathlib's `HenselianRing`.
- Completeness and nonarchimedeanity are explicit hypotheses (`IsCompleteForAbsoluteValue`, `NonarchimedeanAbsoluteValue`); the absolute value takes values in `ℝ`, so the rank is at most one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Complete.lean`: the Lean file is the source byte for byte (SHA-256 `a51aa334ce7f314c89d6fbe767958afc38cf3af3bcb0cd9d8e8b4712b737f310`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
