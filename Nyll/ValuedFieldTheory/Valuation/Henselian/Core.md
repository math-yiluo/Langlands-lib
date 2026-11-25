# Hensel's lemma in factorization form: definitions

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines Henselianity of a valuation through lifting of coprime factorizations, records small lemmas on residual linear factors, and shows that a finite algebra over a noetherian, Henselian and precomplete ring is Henselian along the extended ideal. It also imports the files that prove the factorization form of Hensel's lemma.

## Definitions

- `HenselFactorizationProperty V`, for a valuation subring `V` of a field: for every polynomial `f` over `V` whose reduction is nonzero and equals `ḡ · h̄` with `ḡ`, `h̄` coprime over the residue field, there are `G`, `H` over `V` with `f = G · H`, `deg G = deg ḡ`, `deg H ≤ deg f − deg ḡ`, and reductions `ḡ` and `h̄`.
- `HenselianValuationByFactorization v`: the valuation ring of `v` has this property.

## Results

- For an ideal `J` of a ring `S` and `a₀` with `p(a₀) ∈ J`: the reduction of `p` vanishes at `a₀ mod J` and splits off the factor `X − ā₀`; if moreover `p'(a₀)` is a unit modulo `J`, that factor is coprime to the cofactor (`isCoprime_residual_X_sub_C_divByMonic_of_simpleRoot_mod`). Likewise `isCoprime_X_sub_C_divByMonic_of_derivative_isUnit`: if `p'(a)` is a unit, `X − a` is coprime to `p /ₘ (X − a)`.
- `henselianRing_map_algebraMap_of_moduleFinite_of_base_isPrecomplete`: if `R` is noetherian, Henselian along `I` and `I`-adically precomplete, and `S` is a module-finite `R`-algebra, then `S` is Henselian along `I S`.

## Proofs

The last result gets separatedness from the Jacobson condition of a Henselian pair (with noetherianity), so `R` is `I`-adically complete, and applies the finite-module completeness result of an imported file.

## Caveats

- Both definitions are the library's own and differ from Mathlib's `HenselianRing`: `f` need not be monic, only its reduction must be nonzero; `G` and `H` need not be monic; and only an inequality is required on `deg H`.
- This file only states the definitions; it does not prove that any valuation satisfies them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Core.lean`: the Lean file is the source byte for byte (SHA-256 `436dc704807f8ab0ad3a4f5e8c241e79315363ba29f8bd3923094c84d5a36f4b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
