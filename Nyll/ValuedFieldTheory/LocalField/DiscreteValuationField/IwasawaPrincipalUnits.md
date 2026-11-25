# Iwasawa's product decomposition of principal units in equal characteristic

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field `F` (the library's `LocalField` structure on a field `K`) with residue field `k` of characteristic `p`, uniformizer `π` and higher principal units `U^n`, the file constructs Iwasawa's explicit description of `U^1`: in equal characteristic, `U^1` is isomorphic as a topological group to a product of copies of `ℤ_p^f`, one for each degree `n ≥ 1` prime to `p`, where `|k| = p^f`.

## Finite level

`iwasawaResidueRank F` is `f`, the dimension of `k` over `F_p` (with `|k| = p^f` proved), and `iwasawaResidueBasis F` is a chosen `F_p`-basis `ω_1, …, ω_f`. The seed units `1 + [ω_i] π^n`, with `[·]` the Teichmüller lift, have leading coefficient `ω_i` in `U^n/U^(n+1) ≅ k`. `iwasawaGn F hpi n hn` is the `ℤ_p`-linear map `ℤ_p^f → U^1` (written additively) sending `a` to `∏ (1 + [ω_i] π^n)^(a_i)`. Its values lie in `U^n`, the leading coefficient of `g_n(a)` is `Σ (a_i mod p) ω_i`, and hence `U^n = g_n(ℤ_p^f) U^(n+1)` (`exists_iwasawaGn_mul_mem_succ`), in any characteristic.

Assuming `[CharP K p]`, with `m = n p^s`:
- `exists_iwasawaGnScaled_mul_mem_succ`: `U^m = g_n(p^s ℤ_p^f) U^(m+1)`;
- `iwasawa_formula_two`: `g_n(p^s a)` lies outside `U^(m+1)` exactly when `a` is not divisible by `p` (`IwasawaPrimitive`);
- `principalUnit_residueCharacteristic_smul_eq_zero`: `U^1` has no `p`-torsion;
- `iwasawaGn_injective`: each `g_n` is injective.

These rest on `(1 + x)^(p^s) = 1 + x^(p^s)` in characteristic `p`.

## The infinite product

`iwasawaDomain F` is the full product of `ℤ_p` over `IwasawaIndex p f`, indexed by a degree `n ≥ 1` prime to `p` and an index `i < f`. The partial products `iwasawaPartialProduct` (factors of degree `≤ r`) are compatible in the quotients `U^1/U^(r+1)` and define `iwasawaGlobalProdiscreteLimitAddHom` into `PrincipalUnitProdiscreteLimit`, the library's inverse-limit model of `U^1`. It is continuous. Under `[CharP K p]` it is surjective (each depth `m = n p^s` is reached by induction, then compactness) and injective (a nonzero family has a least depth `n p^s`, unique by `iwasawaDepth_eq_iff`, whose factor survives modulo `U^(m+1)` while all others vanish). The packaged isomorphisms are `iwasawaGlobalProdiscreteLimitContinuousAddEquiv` and `iwasawaGlobalAdicPrincipalUnitsContinuousAddEquiv : iwasawaDomain F ≃ₜ+ AdicPrincipalUnits F.toCompleteDVF`.

## Points to watch

- `iwasawa_formula_two`, injectivity, surjectivity and the global isomorphisms assume `CharP K p`. The maps, the unscaled congruence and continuity do not need it; no decomposition is proved in mixed characteristic.
- The isomorphisms depend on `π` and on a non-canonical basis chosen by `Module.finBasis`.
- The targets are the library's own type-level models of `U^1`, written additively, carrying the adic or prodiscrete topology. The domain is a full product, not a direct sum.
- The `p`-adic powers are the library's own construction through finite principal-unit quotients.
- Declarations under `Internal`, such as the map `Internal.iwasawaGlobalAddHom` into `U^1`, are plumbing.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/IwasawaPrincipalUnits.lean`: the Lean file is the source byte for byte (SHA-256 `4b6e5a01d7c450b87c636750b8040c117ae97fcc713f236f6a6d178314394d97`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
