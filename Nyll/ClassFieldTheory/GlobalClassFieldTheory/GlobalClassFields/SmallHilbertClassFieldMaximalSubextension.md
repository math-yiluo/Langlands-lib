# The small Hilbert class field is the maximal unramified abelian extension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library selects a small Hilbert class field `smallHilbertClassField K` of a number field K in an imported file. It also presents this field inside the rational absolute class formation. There it is a finite abelian subextension `smallHilbertClassFieldSubextension K` over a fixed-field base `smallHilbertClassFieldBase K`, a copy of K inside the separable closure of ℚ. This file shows that this field is the largest finite abelian extension of K that is unramified at all finite and infinite places.

## Main definitions and results

- `smallHilbertClassFieldSubextension_normSubgroup`: in the rational class formation, the norm subgroup of the selected subextension is exactly `smallHilbertNormSubgroupInRationalClassFormation`. That subgroup is the intrinsic small-Hilbert norm subgroup of the fixed-field base (classes of ideles whose finite components are all local units), carried by the fixed-field idele-class equivalence into the fixed part of the rational idele-class representation.
- `finiteAbelianSubextensionIsEverywhereUnramified K P`: for a finite abelian subextension P of the base, the predicate that its fixed field is unramified over the base at every place (`IsEverywhereUnramified`).
- `everywhereUnramifiedAbelianSubextension_le_smallHilbertClassFieldSubextension`: every such everywhere-unramified P lies below the selected subextension.
- `smallHilbertClassFieldSubextension_isEverywhereUnramifiedAndMaximalAbelian`: the small Hilbert class field is everywhere unramified over K, and it is maximal in the sense just stated.
- `finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified`: let L be a number field that is a finite abelian Galois extension of K. Assume L/K is unramified at the infinite places and that no finite place of K ramifies in L. Then there is a K-algebra map L → `smallHilbertClassField K`.

## Proof

The norm-subgroup identity is checked after mapping back along the idele-class equivalence of the fixed-field base. There it reduces to two imported facts: the abstract norm subgroup is the ordinary idele-class norm range, and the norm range of the small Hilbert class field is the intrinsic subgroup. Maximality then follows from the imported order-reversing classification of finite abelian subextensions. The embedding theorem compares norm ranges: the intrinsic subgroup lies in the norm range of every everywhere-unramified abelian extension.

## Points to watch

- Maximality is stated for subextensions of the selected base inside the separable closure of ℚ. For a finite abelian extension L of K that is everywhere unramified but given abstractly, the file gives only the existence of an embedding (`Nonempty`). It gives neither uniqueness nor a canonical choice.
- "Everywhere unramified" includes the infinite places. Extensions ramified only at real places are not covered.
- Several private declarations only transport subgroups along the equivalence.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/SmallHilbertClassFieldMaximalSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `467c9b9bd70401aa5558d6a3ac204643c94bdc0c70382f72fdf76a610ce0bc58`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
