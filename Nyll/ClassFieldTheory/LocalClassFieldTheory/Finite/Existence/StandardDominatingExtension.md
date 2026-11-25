# Finite abelian extensions embed in standard Lubin–Tate composita

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardDominatingExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `L / K` a finite abelian Galois extension. This file shows that `L` embeds over `K` into the fixed field, inside `SeparableClosure K`, of a standard finite abelian extension built from an unramified factor and a Lubin–Tate factor. The argument does not depend on the characteristic.

- `exists_finiteAbelianDominatingStandardLubinTateCompositum`: there are `d > 0` (the unramified degree) and `n > 0` (the principal-unit level) and a `K`-algebra map from `L` into the fixed field of `standardLubinTateFiniteAbelianCompositum K d n hd`.
- `exists_finiteAbelianDominatingStandardFixedField`: the same with the parameters forgotten: some abstract finite abelian subextension `P` has a fixed field receiving `L`.

Proof: with `ϖ := inverseIntegerRingUniformizerFieldUnit K`, the norm subgroup of `L` contains a standard subgroup built from `ϖ ^ d` and `U^(n)` (`exists_uniformizerPrincipalSubgroup_le_normSubgroup`). The norm subgroup of the standard compositum lies inside it (`standardLubinTateFiniteAbelianCompositum_nativeNormSubgroup_le`), and reverse inclusion of norm subgroups yields the embedding (`nonempty_algHom_of_normSubgroup_le`).

Both `K` and `L` are taken in universe `0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardDominatingExtension.lean`: the Lean file is the source byte for byte (SHA-256 `295a0e526e86603873a0d75324e7b80b74491c9ab0aeb8e80726c106a25a0fac`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
