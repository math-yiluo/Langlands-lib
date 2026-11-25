# Relative and ordinary idele class groups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields `K ⊆ L`, the library has two models of the idele class group of `L`: the relative one, units of `𝔸_K ⊗_K L` modulo `Lˣ`, and the ordinary restricted-product one, `IdeleClassGroup L`. The file passes the comparison of ideles `relativeIdeleBaseChangeMulEquiv` to idele classes and identifies the inclusion of `C_K` on both sides.

## Main declarations

- `relativeIdelePrincipalSubgroup_map_baseChange`: the comparison maps the relative principal ideles onto the principal ideles of `L`.
- `relativeIdeleClassBaseChangeMulEquiv : RelativeIdeleGroup.ClassGroup K L ≃* IdeleClassGroup L`, the induced isomorphism of quotients; `relativeIdeleClassBaseChangeMulEquiv_mk` computes it on representatives.
- `relativeIdeleClassBaseChangeMulEquiv_classInclusion` and `relativeIdeleClassBaseChange_comp_classInclusion`: under this isomorphism, the relative class inclusion `RelativeIdeleGroup.classInclusion` is the extension map `ideleClassExtension K L` on ordinary idele classes. Both hold by definition on representatives.

## Points to watch

- The header speaks of a finite Galois extension, but the declarations here carry no finiteness or Galois hypothesis of their own.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/IdeleClassBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `05d61f9c641e0ce3e01ed5c57a649fda84fd83b159cee5054a1e4a20d051c00d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
