# The abelian local Artin map for fields in any universe

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's abelian local Artin map, first built for fields in `Type`, is extended to a nonarchimedean local field K : Type u and a finite abelian Galois extension L : Type v. K and L are replaced by small copies `Shrink.{0} K` and `Shrink.{0} L`, the native map is applied there, and the result is carried back along the field equivalences `Shrink.ringEquiv` and the induced Galois-group isomorphism `HasseArf.shrinkGalMulEquiv`. All declarations live in the namespace `LocalClassFieldTheory.Universe`.

## Main definitions and results

Hypotheses throughout: `ValuativeRel K`, a topology on K, `IsNonarchimedeanLocalField K`, `FiniteDimensional K L` and `IsAbelianGalois K L`.

- `abelianLocalArtinMap : Kˣ →ₜ* Gal(L/K)` and its underlying homomorphism `abelianLocalArtinMonoidHom`.
- `abelianLocalArtinMap_apply_shrink`: the image of a acts on L as the transported action of the native Artin image of the corresponding unit of the small copy of K.
- `abelianLocalArtinMap_surjective` and `abelianLocalArtinMap_ker`: the map is surjective and its kernel is the field-norm subgroup `ClassFieldTheory.fieldNormSubgroup K L`; the same for `abelianLocalArtinMonoidHom`, with the kernel written as `localNormSubgroup K L`. The kernel statement uses that ring equivalences carry norm subgroups to norm subgroups.
- `quotientEquiv_existsUnique`: there is exactly one isomorphism of topological groups `FieldNormQuotient K L ≃ₜ* Gal(L/K)` sending the class of a to the Artin image of a, obtained from `ClassFieldTheory.finiteAbelianLocalReciprocity_quotientEquiv_of_artin`.
- `shrink_semilinearValuationCompatible`: the equivalence from K to `Shrink.{0} K` is compatible with the two valuation relations.
- `abelianLocalArtinMap_eq_native`, `abelianLocalArtinMonoidHom_eq_native`: when K and L lie in `Type`, the transported map equals the original `_root_.LocalClassFieldTheory.abelianLocalArtinMap`, and its underlying homomorphism equals the original `_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom`. The proof applies the semilinear naturality of the Artin action, `abelianLocalArtinMonoidHom_semilinear_action`, to the two shrinking equivalences.

## Caveats

- The names repeat those of the `Type`-level maps in the root namespace `LocalClassFieldTheory`; only the namespace `Universe` tells them apart.
- The definition goes through the particular small models given by `smallLocalField K` and `Module.Finite.small K L`. The module docstring stresses that no isomorphism of the Galois group is taken from a norm-quotient existence theorem.
- Only finite abelian extensions are treated, and the target is `Gal(L/K)` itself.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseArtin.lean`: the Lean file is the source byte for byte (SHA-256 `51ffb3746dddc6d8d5c72af415708f1cbf983dad42b47dad3acfaceb1c96b247`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
