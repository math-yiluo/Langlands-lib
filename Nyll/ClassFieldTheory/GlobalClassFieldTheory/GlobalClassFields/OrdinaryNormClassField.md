# Class fields for subgroups containing a norm group

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.OrdinaryNormClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields and `H` a subgroup of the idèle class group `C_K` containing the norm group `N(C_L)`. The file constructs a finite abelian extension whose idèle-class norm group is `H`. It realizes `K` inside the rational absolute class formation, on the idèle classes over the separable closure of `ℚ`, as the fixed field of `numberFieldTowerBaseSubgroup K L`. There the transported `H` is norm-open, so the library's finite abelian classification for class formations supplies a subextension with that norm subgroup. The result is then transported back to ordinary idèle class groups.

## Main definitions and results

- `exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le`: there is a finite abelian subextension `M` over the base subgroup whose abstract norm subgroup is the image of `H`. This uses the imported facts that the transported subgroup is norm-open, that the rational idèle-class representation satisfies the class field axiom, and that the norm-subgroup map of finite abelian subextensions is surjective.
- `numberFieldTowerBaseTransport_isOpen_of_normRange_le`: the image of `H` in the idèle class group of the fixed-field copy of `K` is open for the usual topology. This compares the norm topology with the idèle-class topology.
- `ordinaryNormClassFieldSubextension`: the chosen `M` (by `Classical.choose`), with `ordinaryNormClassFieldSubextension_normSubgroup`.
- `ordinaryNormClassFieldBase K L`: the fixed-field copy of `K`, a number field, with `ordinaryNormClassFieldBaseEquiv : K ≃ₐ[ℚ] ordinaryNormClassFieldBase K L`.
- `ordinaryNormClassFieldExtension K L H hLH`: the relative fixed field of `M`, with instances making it a number field and a finite abelian Galois extension of `ordinaryNormClassFieldBase K L`.
- `ordinaryNormClassField_ideleClassNorm_range`: the image of the ordinary idèle-class norm of this extension is the image of `H` under `ideleClassCongr` of the base isomorphism (an equality of additive subgroups).

The last result combines an imported comparison between the abstract norm subgroup of a finite subextension and the ordinary idèle-class norm range with the compatibility of the various transport isomorphisms.

## Points to watch

- The class field is an extension of `ordinaryNormClassFieldBase K L`, a field isomorphic to `K` over `ℚ` that depends on `L`, not of `K` itself. Its norm group is `H` only after transport.
- `H` is not assumed closed, open or of finite index; containing `N(C_L)` is the only hypothesis, and openness is derived.
- The construction rests on the abstract class formation for `ℚ` and on the class field axiom for it, both imported.
- The field is selected by choice, so only its stated properties are available.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/OrdinaryNormClassField.lean`: the Lean file is the source byte for byte (SHA-256 `e929cbc96137372d31447dc9e0240f1d125a29781eaff8684785a246228badf2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
