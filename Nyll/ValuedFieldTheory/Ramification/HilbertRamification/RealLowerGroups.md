# Lower ramification groups with real index

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a field extension with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, and let O_L be the valuation ring of L with maximal ideal m_L. The file defines what it means for the valuation of K to extend uniquely to L, derives from it that Gal(L/K) acts on O_L, and defines the lower ramification groups G_s for every real s. It then proves their elementary properties and their behaviour under change of the base field. Completeness is not assumed.

## Unique extension

- `DVF.HasUniqueValuationExtension base target`: every valuation of L extending the valuation of K is equivalent to the valuation of `target`.
- `mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension`: under this hypothesis every K-automorphism σ of L preserves O_L, because the valuation of `target` composed with σ is again an extension.
- `valuationSubringAutOfUniqueExtension huniq σ`: the induced ring automorphism of O_L, with simp lemmas for the identity, products and inverses. It preserves m_L and all its powers.

## Real index

- `realRamificationExponent s`: the natural number ⌈s + 1⌉, truncated at 0. It is monotone, equals 0 for s ≤ −1, and equals n + 1 at s = n.
- `realRamificationIdeal target s`: the ideal m_L raised to that exponent. It is antitone in s, equals O_L for s ≤ −1, and equals m_L^(n+1) at s = n.
- `lowerRamificationGroup huniq s`: the σ in Gal(L/K) with σ(a) − a in `realRamificationIdeal target s` for every a in O_L. At s = n this is the condition σ(a) − a ∈ m_L^(n+1). The groups are antitone in s and normal (`lowerRamificationGroup_normal`, also an instance), and they equal Gal(L/K) for s ≤ −1.

## Change of base field

For an intermediate field M, `galRestrictScalarsToIntermediate M` is the injective map Gal(L/M) → Gal(L/K), whose image is the fixing subgroup of M. `lowerRamificationGroupOverIntermediate huniq M s` is the preimage of G_s. `lowerRamificationGroupOverIntermediate_map_eq_inf` states that its image in Gal(L/K) is G_s ∩ Gal(L/M).

## Watch for

- In its uses here, `HasUniqueValuationExtension` is instantiated at the universe level `x` of the valuation of `target`. Uniqueness is then required only among valuations whose value groups lie in that universe.
- Equivalent valuations are allowed in that definition, so it concerns the valuation ring, not the valuation itself.
- G_s depends on s only through ⌈s + 1⌉. The groups over M are defined with the valuation ring of L and K's uniqueness hypothesis, not with a structure on M, so the change-of-base statement holds by construction.
- No finiteness of L/K is assumed in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`: the Lean file is the source byte for byte (SHA-256 `5e63ffb712b9b2b50d2b1c1fd4dd089596055157b93f8771bec31a2425d53378`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
