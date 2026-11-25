# The ℤ_p-action on principal units: first properties

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field in the library's sense (`LocalField`) with residue characteristic `p`, and `U^r` its higher principal unit groups. The first principal units `U^1`, written additively, carry a ℤ_p-module structure built in the imported files from the inverse limit of the quotients `U^1 / U^(n+1)`. This file gathers those models and proves the first properties of the action.

- `principalUnitPadic_natCast_smul` and `principalUnitPadic_nsmul_eq_pow` (simp lemmas): a natural number `n`, viewed in ℤ_p, acts on `x` in `U^1` as the power `x^n`.
- `principalUnitPadic_smul_mem_higher`: for `r ≥ 1`, each `U^r` is stable under the action. If `x` lies in `U^r`, so does `a • x` for every `a` in ℤ_p. Proof: `x` has trivial image in `U^1 / U^r`, and the map to that coordinate of the inverse limit is ℤ_p-linear, so `a • x` has trivial image too.
- `principalUnitPadic_residueCharacteristic_mul_smul_mem_succ`: for `r ≥ 1` and `x` in `U^r`, `(p·b) • x` lies in `U^(r+1)` for every `b` in ℤ_p. Proof: `(p·b) • x = b • x^p`, the `p`-th power maps `U^r` into `U^(r+1)` by a lemma from elsewhere in the library, and the previous result applies.

Watch for:

- The action is the library's own construction, defined by transport from the inverse limit, with `p` given as `F.residueCharacteristic`. Elements are taken in `U^1` and their membership in `U^r` is stated through the coercion to the units of the valuation ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitPadicAction/Core.lean`: the Lean file is the source byte for byte (SHA-256 `0347ad8f501fbaf035eda2a48911e98c3b20c10b52f8a2298b26f4f47ac6e83e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
