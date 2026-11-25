# Lifting residue points of étale algebras over a Henselian pair

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.EtaleLifting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `R` be Henselian along a maximal ideal `I` (Mathlib's `HenselianRing`) and `S` an étale `R`-algebra.

`exists_etale_lift`: every `R`-algebra map `σ : S → R ⧸ I` lifts to an `R`-algebra map `τ : S → R`, that is, `τ` followed by the quotient map is `σ`.

## Proof

The kernel `Q` of `σ` is prime. By Mathlib, an étale algebra has, at `Q`, an element `s ∉ Q` whose localization `S[1/s]` is standard étale. Since `σ(s)` is nonzero in the field `R ⧸ I`, `σ` extends to `S[1/s]`; that point lifts to `R` by the standard-étale lifting result of an imported file, and composing with `S → S[1/s]` gives `τ`.

## Caveats

The ideal `I` must be maximal, so `R ⧸ I` is a field; this is the residue-point case, not lifting along an arbitrary Henselian ideal.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/EtaleLifting.lean`: the Lean file is the source byte for byte (SHA-256 `5f82b4b325b72d11a343e0682bc66a58671a51bc580076814bb801e426f503dc`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
