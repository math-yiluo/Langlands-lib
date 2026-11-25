# Norms from the unramified extension of degree d

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K`, the canonical unramified extension of degree `d` is built abstractly inside the library's class formation for `K`, from the residue-degree data `localResidueDatum K` over the base `intrinsicFiniteAbstractBase K`; the valuation data `localHenselianValuation K` enters only the proof. This file shows that its norm subgroup, transported from the abstract fixed-coefficient description to `Kˣ`, lies in `unramifiedNormSubgroup K d`, the subgroup of elements whose normalized valuation is divisible by `d`.

## Main definitions and results

- `finiteUnramifiedNormSubgroup_map_le_unramifiedNormSubgroup`: for `d > 0`, the transported norm subgroup of `DegreeData.finiteUnramifiedExtension D Kresidue d hd` is contained in `unramifiedNormSubgroup K d`.
- `exists_unramifiedFiniteGaloisExtension_normSubgroup_map_le`: the same, stated as the existence of a finite Galois subextension with this property.
- `localFiniteUnramifiedAbelianSubextension K d hd`: the canonical degree-`d` unramified factor, retained as a finite abelian subextension of the absolute Galois group.
- `localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le` and `exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le`: the same containment for this abelian factor.

## Proof

The tower formula for the normalized valuation (`normalizedValuation_tower`) gives: the valuation of a relative norm equals the residue degree, which is `d` by `finiteUnramifiedExtension_residueDegree`, times the valuation of the element, with values in `ℤ̂`. The abstract valuation at the base field is then identified with the valuation of `K` (`localBaseValuation_baseFieldUnitsEquiv`), and reduction `ℤ̂ → ℤ/dℤ` (`zHatReduction`) gives divisibility by `d`. Two private lemmas handle the different, propositionally equal presentations of the base field.

## Points to watch

- Only one containment is proved: norms have valuation divisible by `d`. That every such element is a norm is not stated here.
- The unramified extension is an abstract object of the class-formation framework, a closed subgroup of the absolute Galois group, not a concrete field extension of `K`.
- The abstract valuations take values in `ℤ̂`; comparison with the integer-valued valuation of `K` is part of the proof.
- The theorems take `K : Type`; the definition allows any universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormContainment.lean`: the Lean file is the source byte for byte (SHA-256 `6886de741762eb24164aaf1db26697b0526ec4d12e12752f2868a9367731a266`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
