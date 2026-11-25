# Exact torsion level of the primitive Lubin–Tate roots

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a local field with uniformizer π and residue field of q elements, f(X) = X^q + π·X, and λₙ the root of the primitive polynomial Qₙ = (f^[n])^(q−1) + π chosen in `SeparableClosure K`. The file shows that λₙ is a point of exact level n + 1 for the iterates of f: f^[n+1](λₙ) = 0 but f^[n](λₙ) ≠ 0. The arguments do not depend on the characteristic.

## Main definitions

- `standardLubinTatePolynomialIterateOverField F π n` and `standardLubinTatePolynomialIterateOverSeparableClosure F π n`: the iterate f^[n] with coefficients mapped into K, respectively into `SeparableClosure K`.

## Main results

- `standardLubinTatePolynomialIterate_eval₂_eq_iterate`, `standardLubinTatePolynomialIterate_eval₂_add`, `standardLubinTatePolynomialIterateOverSeparableClosure_eval_add`: evaluating f^[n] is the n-th iterate of evaluating f, so evaluations of f^[m+n] factor through f^[n] then f^[m], over any commutative semiring receiving the valuation ring.
- `standardLubinTatePrimitivePolynomialOverField_eval₂`, `chosenStandardLubinTatePrimitiveRoot_equation`: the chosen root satisfies (f^[n](λₙ))^(q−1) + π = 0.
- `chosenStandardLubinTatePrimitiveRoot_iterate_succ_eq_zero`: f^[n+1](λₙ) = 0.
- `chosenStandardLubinTatePrimitiveRoot_iterate_ne_zero`, `chosenStandardLubinTatePrimitiveRoot_ne_zero`: f^[n](λₙ) ≠ 0, hence λₙ ≠ 0.
- `chosenStandardLubinTatePrimitivePredecessor_isRoot`: for m ≤ n, f^[n−m](λₙ) is a root of Qₘ.

## Proofs

The vanishing of f^[n+1](λₙ) comes from a factorization of f^[n+1] with Qₙ as a factor, proved in the division-polynomial file. Nonvanishing of f^[n](λₙ) follows from the primitive equation, since otherwise π = 0. The predecessor statement uses additivity of iterate indices.

## Watch for

- These are statements about polynomial iterates of f evaluated in the separable closure, not about a formal-group module structure.
- λₙ is a single chosen root, and its exact level is n + 1, one more than its index.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveTorsion.lean`: the Lean file is the source byte for byte (SHA-256 `99df5e29edb4751edcc2776cd5124b9a3f68ebbd412607568b82d5b42ac27982`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
