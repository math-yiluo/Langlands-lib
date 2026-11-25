# Ideles built from finitely many local components

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteLocalFamily`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A finite family of local units, one at each finite place v in a finite set S of a number field K and extended by 1 elsewhere, defines an idele of K. This file shows that this idele is the product of the one-place ideles, so that any homomorphism out of the idele group, in particular the global norm-class map, turns it into a finite product of local values.

## Main results

- `prod_finitePlaceIdele_eq_ideleOfFiniteLocalFamily`: for S a finite set of height-one primes of 𝓞 K and a_v ∈ K_vˣ for v ∈ S, the product over v ∈ S of `finitePlaceIdele v a_v` is `IdeleGroup.ideleOfFiniteLocalFamily S a`. The proof compares the infinite components (all 1) and the finite components place by place.
- `map_ideleOfFiniteLocalFamily_eq_prod_local`: for any homomorphism f from the idele group of K to a commutative group, f of that idele is the product over v ∈ S of f(`finitePlaceIdele v a_v`).
- `globalNormClass_finiteLocalFamily`: the special case of `globalNormClassFromIdele K L`, the map from ideles of K to the norm quotient for a number field L over K.

## Points to watch

- Only finite places occur in the family; the infinite components are 1.
- The module comment also says that the norm-class map factors through idele classes and kills principal ideles. That fact belongs to the imported definition; this file neither states nor proves it.
- The idele class group of K is given its commutative group structure by local instances here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteLocalFamily.lean`: the Lean file is the source byte for byte (SHA-256 `e7074c5bd93700b56c1ea471705f96ea1955df2d6d083c041d7dbd1264ca14ca`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
