# Finite levels of the rational idele-class direct limit

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteLevelCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file attaches to every finite intermediate field `K` of `ℚˢᵉᵖ/ℚ`, Galois or not, a canonical map from its idele class group `C_K` into `rationalIdeleClassDirectLimit`, passing through the normal closure of `K`, and proves that these maps are compatible with inclusions of fields.

## Main definitions

- `rationalNormalClosure K`: the normal closure of `K` inside `ℚˢᵉᵖ`, packaged as a finite Galois intermediate field.
- `rationalBaseFixingCosetEquivNormalClosure K`: a bijection between the cosets of `Gal(ℚˢᵉᵖ/K)` in the whole group (written with closed fixing subgroups) and the `ℚ`-embeddings of `K` into its normal closure.
- `rationalIntermediateIdeleClassToNormalClosure K`: `C_K` to the relative idele class group at the normal closure, the inverse base change followed by scalar extension.
- `rationalIntermediateIdeleClassToDirectLimit K`: its composite with the map from that level into the direct limit.
- Global instances giving a commutative group structure on the tower idele class group `TowerRelativeIdeleGroup.ClassGroup ℚ K N`.

## Main results

- `rationalIntermediateIdeleClassToDirectLimit_baseChange`: on a class given in the relative presentation over `ℚ`, the map is scalar extension to the normal closure followed by the level map.
- `rationalFiniteGaloisIdeleClassToDirectLimit_baseChange`: for finite Galois `E`, it agrees with the level map `rationalRelativeIdeleClassToDirectLimit E`.
- `rationalIntermediateIdeleClassToDirectLimit_extension`: for `F ≤ E`, the maps for `F` and `E` agree after scalar extension from `F` to `E`.

The proofs use the defining relation of the direct limit, monotonicity of normal closures and a private commutative square of scalar extensions.

## Points to watch

- The maps are defined through the chosen normal closure; their injectivity is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitFiniteLevelCore.lean`: the Lean file is the source byte for byte (SHA-256 `fe09b6c8c15e6d19ab16e597e4cf04ad220a3babfe370ba6b94ef6248a304bca`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
