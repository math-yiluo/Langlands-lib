# Continuity of transported finite completions

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields K and M with a ℚ-algebra isomorphism e : K ≃ M, and a finite place W of M, this file proves that the library's map `finitePlaceAdicCompletionCongrHom e W`, from the adic completion of K at the corresponding place to the completion of M at W, is continuous.

- `finitePlaceAdicCompletionCongrHom_continuous`: the map is continuous.

It is an instance of the general continuity of completion maps `finitePlaceAdicCompletionMap_continuous`, after making M a K-algebra through e. It provides the local continuity needed to transport the restricted-product topology of the adeles.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquivTopology.lean`: the Lean file is the source byte for byte (SHA-256 `9ad24e2e5431c029e7f16f617112e01e0a85df893e4747460fd95cc3a91905ed`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
