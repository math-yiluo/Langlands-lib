# Hensel's lemma over a complete nonarchimedean field

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Complete`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field with a real-valued absolute value `v` that is nonarchimedean and complete, and `O` its valuation ring (`absoluteValueValuationSubring v`).

`henselFactorization_complete_exists_factorization`: if a polynomial `f` over `O` has nonzero reduction `f̄`, and `f̄ = ḡ · h̄` with `ḡ`, `h̄` coprime over the residue field, then `f = G · H` over `O` with `G` reducing to `ḡ`, `H` reducing to `h̄`, and `deg G = deg ḡ`.

## Proof

For each nonzero `π` in the maximal ideal, `O` is `π`-adically precomplete and separated (imported results), so the principal-ideal form of Hensel's lemma for valuation rings applies.

## Caveats

- "Primitive" in the file means only that the reduction of `f` is nonzero; `f`, `G`, `H` need not be monic.
- The bound `deg H ≤ deg f − deg ḡ`, available from the underlying theorem, is dropped from this statement.
- Completeness and nonarchimedeanity are the explicit hypotheses `IsCompleteForAbsoluteValue v` and `NonarchimedeanAbsoluteValue v`; the absolute value is real-valued, so the rank is at most one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/Complete.lean`: the Lean file is the source byte for byte (SHA-256 `f861eb1adce7116853c20179e2c29a88a01626e99eba7bcb1426f4449c7c6248`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
