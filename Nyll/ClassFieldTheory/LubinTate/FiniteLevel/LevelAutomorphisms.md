# Automorphisms of standard Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, `π` a uniformizer, and `L_n` the standard Lubin–Tate level `n`, the field generated over `K` by a chosen primitive division point `λ`, of degree `(q − 1)·q^n`. The file turns each finite unit parameter `a ∈ O_Fˣ / U^(n+1)` into a `K`-automorphism of `L_n` sending `λ` to `[a](λ)`, and shows that this gives all automorphisms; hence `L_n/K` is Galois.

## Main definitions and results

- `standardLubinTateUnitParameterLevelRoot`: the root `[a](λ)` as an element of `L_n`. Distinct parameters give distinct roots, the trivial parameter gives the generator, and each root is a root of the minimal polynomial of `λ`.
- `standardLubinTateUnitParameterAlgHom`, `standardLubinTateUnitParameterAlgEquiv`: the `K`-endomorphism of `L_n` sending `λ` to `[a](λ)` (lifted along the power basis), which is an automorphism since `L_n` is finite-dimensional.
- `standardLubinTateUnitParameterAlgEquiv_apply_levelRoot`: the automorphism of `a` sends the root of `b` to the root of `a·b`. Hence the map is multiplicative and sends `1` to the identity.
- `standardLubinTateUnitParameterToGal`: the map `O_Fˣ / U^(n+1) → Gal(L_n/K)`; it is injective, multiplicative, and bijective (`standardLubinTateUnitParameterToGal_bijective`, `standardLubinTateUnitParameterToGal_surjective`).
- `standardLubinTateLevelField_natCard_gal`: the automorphism group has as many elements as the degree `[L_n : K]`.
- `standardLubinTateLevelField_isGalois`: `L_n/K` is Galois.

## Proof

Every `K`-automorphism `σ` of `L_n` preserves the valuation ring (the integral closure of `O_F`) and is continuous for its adic topology, so it commutes with evaluating the Lubin–Tate power series `[w]` at `λ`: `σ([w](λ)) = [w](σ(λ))`. With `σ(λ) = [u](λ)` this gives `σ([w](λ)) = [wu](λ)`. Injectivity comes from faithfulness of the action on `λ` modulo `U^(n+1)`. The counting argument: at most `[L_n : K]` automorphisms, and at least `(q − 1)·q^n = [L_n : K]` from the injective map.

## Points to watch

- As in the evaluation file, `O_F` carries the discrete topology and the level valuation ring its maximal-ideal-adic topology, here as private local instances.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/LevelAutomorphisms.lean`: the Lean file is the source byte for byte (SHA-256 `1d465b89a26e7a115413de49a12bd48ee60835e60144efcfe0641dfc09797df0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
