# Ideles supported at a single place

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a place `v`, the local group `K_vˣ` embeds into the idele group by putting a given unit at `v` and `1` everywhere else. This file constructs these embeddings at archimedean and at finite places, their composites with the projection to the idele class group, and the analogous one-place elements of the relative idele group of a finite extension `L/K`, whose components lie in `(K_v ⊗[K] L)ˣ`.

## Main definitions and results

- `IdeleGroup.infinitePlaceIdele v`: for an archimedean place `v`, the homomorphism `K_vˣ →* IdeleGroup K`. It is continuous (`continuous_infinitePlaceIdele`), and `infinitePlaceIdeleContinuous` is the same map as a continuous homomorphism.
- `IdeleGroup.finitePlaceIdele v`: for a finite place `v`, the homomorphism `K_vˣ →* IdeleGroup K`; the restricted-product condition holds because all other components are `1`.
- For both, simp lemmas give the components: the prescribed value at `v` and `1` at every other place, finite or infinite.
- `IdeleGroup.infinitePlaceIdeleClass v` and `IdeleGroup.finitePlaceIdeleClass v`: the composites with the quotient by the principal ideles, landing in `IdeleClassGroup K`.
- `RelativeIdeleGroup.relativeInfinitePlaceIdele v z` and `RelativeIdeleGroup.relativeFinitePlaceIdele v z`: for `z` a unit of `K_v ⊗[K] L`, the relative idele with component `z` at `v` and `1` elsewhere, built from local data through `relativeIdeleOfLocalData`; simp lemmas compute all their components.

## Proof

The relative constructions check the almost-everywhere integrality required by the local data by comparison with the local data of the identity relative idele, which agrees with the new data at all places except `v`.

## Points to watch

- The module comment speaks only of finite places, but the file treats archimedean places as well.
- The relative one-place ideles are defined as plain functions into `RelativeIdeleGroup K L`; the file does not state that they are homomorphisms or continuous.
- Continuity is proved only for the archimedean embedding `infinitePlaceIdele`, not for `finitePlaceIdele`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/SinglePlace.lean`: the Lean file is the source byte for byte (SHA-256 `9fc8bb84efa85cad4c50241208d56679c532e1f850093b96bd9f0327b3f93c2f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
