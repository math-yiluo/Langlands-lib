# The global Artin map agrees with the global norm-residue map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension L/K of number fields, the file shows that the global Artin map on ideles, the product of the chosen local Artin maps, is the pullback along I_K → C_K of the library's global norm-residue map C_K → Gal(L/K). It deduces the product formula on principal ideles and the descent of the Artin map to the idele class group, with its image and kernel.

## Main results

- `globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin`: `globalNormResidueMonoidHom K L` composed with the quotient map I_K → C_K equals `globalArtinMonoidHom`.
- `globalArtinMonoidHom_principalIdele` (simp): the Artin map is trivial on every principal idele. `chosenLocalArtin_product_principalIdele` writes this out as the product formula: for x ∈ Kˣ, the product over infinite places and the finite-support product over finite places of the chosen local symbols of x is 1.
- `globalIdeleClassArtinMonoidHom`: the map C_K → Gal(L/K) induced by `globalArtinMonoidHom`; `globalIdeleClassArtinMonoidHom_mk` evaluates it on representatives. It is continuous for the quotient topology, and `globalIdeleClassArtinContinuousMonoidHom` bundles it as a continuous homomorphism.
- `globalIdeleClassArtinMonoidHom_eq_globalNormResidueMonoidHom`, and its continuous form `globalIdeleClassArtinContinuousMonoidHom_eq_globalNormResidueContinuousMonoidHom`: the descended map is the norm-residue map.
- `globalIdeleClassArtinMonoidHom_surjective`; `globalIdeleClassArtinMonoidHom_ker` and `globalIdeleClassArtinMonoidHom_eq_one_iff` (simp): the kernel is the image of the idele-class norm `ideleClassNorm K L`.

## Proof

An idele a is replaced by `artinFiniteSupportApproximation a`, a product of one-place ideles at the infinite places and finitely many finite places. It has the same norm class (`globalNormClassFromIdele_eq_artinFiniteSupportApproximation`) and the same Artin value (`globalArtinMonoidHom_eq_artinFiniteSupportApproximation`). On a one-place idele the two maps agree by the finite-place and infinite-place compatibility theorems `globalNormResidueMonoidHom_comp_finitePlaceIdeleClass` and `globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass`.

## Points to watch

- Triviality on principal ideles is not proved from the local maps directly: it is read off from the comparison with the norm-residue map, which is defined on C_K. Surjectivity and the kernel are likewise transported from the imported results `globalNormResidueMonoidHom_surjective` and `globalNormResidueMonoidHom_ker`.
- The local maps use the geometric Frobenius normalization; the file's comments point to a module `ArithmeticNormalization` for the arithmetic one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalArtinCompatibility.lean`: the Lean file is the source byte for byte (SHA-256 `793c6e5e7c7b31be1e31605d0c705b3963ae4c557f9e4e9a33f692cda8f7c396`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
