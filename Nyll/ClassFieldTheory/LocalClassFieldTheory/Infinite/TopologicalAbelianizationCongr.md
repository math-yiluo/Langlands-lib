# Topological abelianization is functorial for isomorphisms

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For topological groups G and H, an isomorphism of topological groups e : G ≃ₜ* H carries the closure of the commutator subgroup of G into that of H, and so descends to an isomorphism of the topological abelianizations (the quotients by these closures).

## Main definitions and results

- `topologicalCommutatorClosure_le_comap`: the closure of [G, G] lies in the preimage under e of the closure of [H, H].
- `topologicalAbelianizationMap e`: the induced group homomorphism, with `topologicalAbelianizationMap_mk` on classes and `topologicalAbelianizationMap_continuous`.
- `topologicalAbelianizationMulEquiv e`: the induced group isomorphism, with inverse induced by e⁻¹.
- `topologicalAbelianizationCongr e : TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H`, with the simp lemma `topologicalAbelianizationCongr_mk`.

## Caveats

Only isomorphisms are treated; no map is constructed for a general continuous homomorphism. G and H may lie in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Infinite/TopologicalAbelianizationCongr.lean`: the Lean file is the source byte for byte (SHA-256 `7c2a9d30d926a1ce1474bbf2d2cb1dec642dfbbc8c21d438886587240c64c9ae`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
