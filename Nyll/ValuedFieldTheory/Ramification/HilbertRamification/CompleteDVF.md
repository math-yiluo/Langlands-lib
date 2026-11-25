# Decomposition and inertia for finite extensions of complete discretely valued fields

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite separable extension `L/K` of complete discretely valued fields, the valuation of `K` has a unique extension to `L`, so every `K`-automorphism of `L` preserves the valuation ring of `L` and the whole automorphism group is the decomposition group. The file specializes the general valuation-subring theory of decomposition and inertia groups to this setting and proves the finite Galois exact sequence `1 → I(L/K) → Gal(L/K) → Aut(k_L/k_K) → 1`.

The data are `base : CompleteDVF K` and `target : CompleteDVF L` (the library's structures for complete discretely valued fields), with the hypothesis that the target valuation extends the base one.

## Main results

- `automorphism_stabilizes_valuationSubring` (finite, separable): every `σ : L ≃ₐ[K] L` maps the valuation ring of `L` to itself.
- `galEquivDecompositionGroup` (finite, separable): the group isomorphism from `L ≃ₐ[K] L` to the decomposition group of the target valuation ring.
- `decompositionResidueAction`: reduction, from the decomposition group to the `k_K`-algebra automorphisms of `k_L`; `decompositionResidueAction_ker` identifies its kernel with the inertia group, and `decompositionInertia_mulExact_decompositionResidueAction` states exactness.
- `maximalIdealInertia_eq_decompositionInertia`: the ideal-theoretic inertia group of the maximal ideal (σa − a ∈ 𝔪 for all a) equals the valuation-subring inertia group.
- `residueAction`, `inertiaGroup`, `residueAction_ker`, `inertia_mulExact_residueAction`: the same on the full automorphism group; `inertiaGroup` is normal.
- `residueAction_surjective_of_isGalois` and `decompositionResidueAction_surjective_of_isGalois` (`IsGalois K L`): reduction is surjective.
- `galQuotientInertiaEquivResidueGalois` (`IsGalois K L`): `Gal(L/K)/I ≃* Aut(k_L/k_K)`.

## Proofs

Stabilization comes from uniqueness of the valuation extension (`hasUniqueValuationExtension_of_finite_separable`) applied to the valuation pulled back along `σ`. Surjectivity uses that the valuation ring of `L` is a finite module over that of `K`, makes `Gal(L/K)` a Galois group of the ring extension, and applies Mathlib's surjectivity of `Ideal.Quotient.stabilizerHom`.

## Points to watch

- The residue target is the group of all `k_K`-algebra automorphisms of `k_L`; no separability or perfectness of the residue extension is assumed or used.
- Stabilization and the full-group statements need finite dimension and separability; surjectivity and the quotient isomorphism need `IsGalois K L`.
- `inertiaGroup` here is a subgroup of `L ≃ₐ[K] L`, defined as the preimage of the valuation-subring inertia group under `galEquivDecompositionGroup`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/CompleteDVF.lean`: the Lean file is the source byte for byte (SHA-256 `1071c40b16b1e39f9221afbec8f7dfb2469530b4bd95446ff322617f070ad891`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
