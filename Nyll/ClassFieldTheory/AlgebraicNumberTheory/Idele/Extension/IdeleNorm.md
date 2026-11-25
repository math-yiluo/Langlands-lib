# The idele norm and the idele class norm

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields `K ⊆ L`, the file defines the norm `N : I_L → I_K` on the ordinary ideles and the induced norm `C_L → C_K` on idele classes. The idele norm is not built place by place: it is the determinant norm of the relative model `𝔸_K ⊗_K L`, transported along the comparison `relativeIdeleBaseChangeMulEquiv` with the ordinary ideles of `L`.

## Main declarations

- `IdeleGroup.norm K L : IdeleGroup L →* IdeleGroup K`, the composite of the inverse comparison with `RelativeIdeleGroup.norm`. `norm_relativeIdeleBaseChangeMulEquiv` records that it agrees with the relative norm.
- `IdeleGroup.norm_principalIdele`: the norm of the principal idele of `x ∈ Lˣ` is the principal idele of the field norm `Algebra.norm K x`.
- `ideleClassNorm : IdeleClassGroup L →* IdeleClassGroup K`, induced on quotients since principal ideles go to principal ideles; `ideleClassNorm_mk` computes it on representatives.

## Points to watch

- The local description of this norm, as a product of local norms, is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/IdeleNorm.lean`: the Lean file is the source byte for byte (SHA-256 `197209d0ef3c79e403855ddc9986ac096c4ef1b40d55662ae4ba008c28b3b3e2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
