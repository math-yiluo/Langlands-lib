# Global norms are local norms everywhere

Module `Nyll.ClassFieldTheory.Theorems.NormTheorems.GlobalNormIsEverywhereLocalNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields and x a unit of K.

`globalNorm_isEverywhereLocalNorm`: if x is a norm from L (`IsFieldNorm K L x`), then x is a local norm everywhere (`IsEverywhereLocalNorm K L x`): at every finite place `w` of K, and at every infinite place `w`, the image of x in the completion K_w is the determinant norm of a unit of K_w ⊗_K L.

The proof is direct. If x is the norm of y from L to K, the element 1 ⊗ y of K_w ⊗_K L has norm the image of that norm, by the base-change formula `tensorNorm_includeRight`.

Both predicates are the library's own and are defined in other files; local norms are taken from the tensor product K_w ⊗_K L, without choosing a place of L above `w`. This is the easy direction; no Hasse norm theorem or converse is stated.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/NormTheorems/GlobalNormIsEverywhereLocalNorm.lean`: the Lean file is the source byte for byte (SHA-256 `2042bab0c080beaea51fc613fdb888534502a258281dfc07e7cc63df850ca15c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
