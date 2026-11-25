# The topology of the idele group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the library's idele group `IdeleGroup K` is a product of the infinite ideles and the finite ideles, the latter a restricted product of the local unit groups `K_vˣ` relative to the units of the valuation rings. This file records its topological structure.

## Main results

- `isOpen_finiteLocalUnits`: at a finite place `v`, the units of the valuation ring are open in `K_vˣ`; this is registered as a `Fact` instance, which the restricted-product topology uses.
- Instances: the finite idele group and the idele group are topological groups; the finite idele group, the infinite adele ring, the infinite idele group and the idele group are Hausdorff. Most are found by instance search from earlier results.
- `IdeleGroup.infiniteComponentContinuous v` and `IdeleGroup.finiteComponentContinuous v`: the component at an archimedean or a finite place, as continuous homomorphisms, with simp lemmas for their values.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Topology.lean`: the Lean file is the source byte for byte (SHA-256 `0e83832a144e6ca866446f68611397751587a55693c92cc090e0c8f7d8328f0d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
