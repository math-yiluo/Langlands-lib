# Hensel factorization for henselian valuation rings

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.SimpleRootFactorization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This short file passes from the simple-root form of Hensel's lemma to the factorization form for a valuation ring V of a field K that is a henselian local ring in Mathlib's sense (`HenselianRing V 𝔪`, with 𝔪 the maximal ideal).

- `monicResidualCoprimeFactorLifting_of_henselianRing`: V satisfies `MonicResidualCoprimeFactorLifting`: a monic polynomial whose reduction is a product of coprime monic factors has monic factors lifting them. It is obtained from `ValuationTheory.Henselian.exists_coprime_factor_lift`, proved in an earlier file.
- `henselFactorization_of_henselianRing`: V satisfies `HenselFactorizationProperty`, the library's factorization form of Hensel's lemma for all polynomials with nonzero reduction, with prescribed reductions and degree bounds. It follows by applying `henselianValuationExtension` from the valuation-extension criterion file to the monic lifting.

According to its docstring, the second result needs no completeness or rank assumption: only the henselian property of V is used.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/SimpleRootFactorization.lean`: the Lean file is the source byte for byte (SHA-256 `387489f1162f8d24dabaf986209b7a9678f5cf124c0cdd22a05e1b69b1406b03`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
