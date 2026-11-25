# Topological finite local reciprocity

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field K and a finite Galois extension L/K, the file upgrades the algebraic finite local reciprocity isomorphism to an isomorphism of topological groups between the norm quotient K^×/N(L^×) and the topological abelianization of Gal(L/K), and packages the resulting continuous local Artin map.

## Main results

- `localNormSubgroup_isOpen`: the norm subgroup `localNormSubgroup K L` is open in K^×. Here K : Type u and L : Type v, with `ValuativeRel K`, a topology on K, `IsNonarchimedeanLocalField K`, `FiniteDimensional K L` and `IsGalois K L`; L carries no topology.
- `normQuotient_discrete`: the quotient topology on `NormQuotient K L` is discrete.
- `commutator_topologicalClosure_eq`: in a discrete topological group the commutator subgroup is closed. Hence `topologicalAbelianization_finite_equiv` identifies `Abelianization (Gal(L/K))` with `TopologicalAbelianization (Gal(L/K))`.
- `localReciprocityEquiv : NormQuotient K L ≃ₜ* TopologicalAbelianization (Gal(L/K))`: the inverse of the algebraic isomorphism `abelianizationEquivNormQuotient` followed by that comparison (`localReciprocityEquiv_toMulEquiv`); continuity holds because both sides are discrete.
- `normClassContinuous` and `localArtinMap : Kˣ →ₜ* TopologicalAbelianization (Gal(L/K))`, the continuous local Artin map.
- `localArtinMap_toMonoidHom`: forgetting the topology recovers the algebraic `localArtinMonoidHom`. `localArtinMap_embedding_independent`: after the same comparison it also agrees with `concreteNormResidueSymbolOfEmbedding` built from any K-embedding of L into `SeparableClosure K`.
- `localArtinMap_surjective`; `localArtinMap_ker`: the kernel is the norm subgroup; `localArtinMap_quotientKerEquiv`, the induced first-isomorphism equivalence, with a simp lemma on classes.

## Proof of openness

The norms of the units of the valuation ring of L form a compact, hence closed, subgroup, because the norm is continuous and those units are compact. This subgroup equals N(L^×) ∩ 𝒪_K^×, by the formula v_K(N y) = f · v_L(y), f the residue degree. N(L^×) has finite index, since the quotient is isomorphic to the finite abelianized Galois group; so N(L^×) ∩ 𝒪_K^× is closed of finite index in 𝒪_K^×, hence open, and 𝒪_K^× is open in K^×. For fields in `Type`, the valuation, norm, completeness and local compactness of L are built from the spectral norm; other universes are reduced to `Type` through `Shrink.{0}` copies of K and L.

## Caveats

- Only `localNormSubgroup_isOpen` and `normQuotient_discrete` are universe-polymorphic; `localReciprocityEquiv`, `localArtinMap` and the results after them require K L : Type.
- The topology on `NormQuotient K L` is a local instance of this file (the quotient topology on `Kˣ ⧸ localNormSubgroup K L`).
- The target is the topological abelianization (quotient by the closure of the commutator subgroup), not Mathlib's `Abelianization`; the two are related only through `topologicalAbelianization_finite_equiv`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `d01e911730e1b67894e813e57eb060d53311137d8479bfe8e096ae43fb7b63f1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
