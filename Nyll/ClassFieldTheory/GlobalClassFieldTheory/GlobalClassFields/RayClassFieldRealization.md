# Ray class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a modulus `m` of a number field `K` (`RayClass.Modulus`: a finite part and a set of real places), the ray congruence subgroup `C_K^m` of the idèle class group is closed of finite index. The file defines the ray class field as the library's selected class field of `C_K^m`, proves reciprocity `Gal(K^m / K) ≃ C_K ⧸ C_K^m`, and characterizes containment of abelian extensions in ray class fields.

## The ray class field

- `rayClassField K m`: `closedFiniteIndexClassField` of `C_K^m`. It is built over `rayClassFieldBase K m`, a fixed-field copy of `K` inside the separable closure of `ℚ`, with `rayClassFieldBaseEquiv : K ≃ₐ[ℚ] rayClassFieldBase K m`. It also carries a `K`-algebra structure, described by `rayClassField_algebraMap_original`.
- `rayClassField_ideleClassNorm_range` (over the base, for the transported subgroup) and `rayClassField_ideleClassNorm_range_over_original`: over `K`, the norm group is exactly `C_K^m`.
- `rayClassFieldSubfield`: its image in `SeparableClosure K`, the same for every `K`-embedding (`rayClassFieldSubfield_eq_fieldRange`).

## Containment and uniqueness

For `L/K` finite abelian:

- `nonempty_algEquiv_rayClassField_iff_ideleClassNorm_range_eq`: `L ≃ₐ[K] K^m` exists if and only if `N(C_L) = C_K^m`.
- `nonempty_algHom_to_rayClassField_iff_isDefiningModulus`: `L` embeds in `K^m` if and only if `C_K^m ≤ N(C_L)`.
- `nonempty_algHom_to_rayClassField_narrowOfFinite_iff_narrowFiniteConductor_le`: for a narrow modulus (every real place) with finite part `n`, `L` embeds if and only if its narrow finite conductor is at most `n`. Hence `finiteAbelianExtension_exists_rayClassFieldEmbedding`: `L` lies in some ray class field.
- `ideleClassNorm_narrowFiniteConductor_is_gcd_of_rayClassField_embeddings`: the narrow finite conductor of `L` is the greatest lower bound of the finite parts of the moduli `m` such that `L` embeds in `K^m`.
- If `m ≤ n`, then `K^m` embeds in `K^n` (`rayClassField_nonempty_algHom_of_le`), and `rayClassFieldSubfield_mono` gives an inclusion of subfields.

## Reciprocity and subgroups

- `rayClassFieldGaloisEquivRayClassGroup` and its topological form `rayClassFieldGaloisContinuousMulEquivRayClassGroup`: the reciprocity isomorphism. The global norm-residue symbol of `c` goes to the ray class of `c` (`_globalNormResidue`). `rayClassField_finrank_eq_rayClassGroup_card`: the degree is the ray class number.
- For a subgroup `H` of the ray class group: `rayClassSubgroupFixedField`, its image `rayClassSubgroupSubfield` in `SeparableClosure K`, and `rayClassSubgroupSubextension` as a `FiniteAbelianExtension K`. Its norm group contains `C_K^m` (`rayClassSubgroupSubextension_norm_range`).
- `rayClassSubgroupFixedFieldArtin` and `rayClassSubgroupArtin`: surjections from the ray class group onto the automorphisms of the fixed field, respectively of `rayClassSubgroupSubextension`, with kernel exactly `H`. `rayClassGroupInvHom` is inversion on the ray class group.

## Points to watch

- `rayClassField K m` is one chosen field, built over a copy of `K`; only its stated properties are available, and uniqueness holds up to isomorphism.
- The reciprocity isomorphism is geometrically normalized; `rayClassSubgroupArtin` inverts its input to obtain the arithmetic normalization.
- In the topological reciprocity the ray class group has its quotient topology, discrete because the congruence subgroup is open.
- The conductor criteria concern finite parts only: the embedding criterion is for narrow moduli, the gcd over all moduli.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/RayClassFieldRealization.lean`: the Lean file is the source byte for byte (SHA-256 `ffb795ce5692ad1999775d9305205228db01fbe3f3c916d77ba7b4435d71846b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
