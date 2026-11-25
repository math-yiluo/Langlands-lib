# Intermediate fields under compatible ring isomorphisms

Module `Nyll.ClassFieldTheory.Algebra.IntermediateFieldRingEquivOrderIso`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let Ω/K and Ψ/M be field extensions with ring isomorphisms e : K ≃ M and c : Ω ≃ Ψ compatible with the algebra maps (`hc`: c(a) = e(a) for a ∈ K). This file transports intermediate fields of Ω/K to intermediate fields of Ψ/M by taking images under c.

- `intermediateFieldMapRingEquiv e c hc L`: the image c(L) of an intermediate field L, as an intermediate field of Ψ/M.
- `intermediateFieldMapRingEquivEquiv`: the ring isomorphism L ≃ c(L) given by c, with its value lemma and its compatibility with e and the algebra maps (`…_commutes`).
- `intermediateFieldMapRingEquiv_symm_commutes`: the inverse isomorphisms are compatible as well.
- `intermediateFieldRingEquivOrderIso`: L ↦ c(L) is an order isomorphism between the lattices of intermediate fields of Ω/K and of Ψ/M, with inverse given by c⁻¹ and e⁻¹.

The image is the literal image subfield under c; no other embedding or closure is chosen.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Algebra/IntermediateFieldRingEquivOrderIso.lean`: the Lean file is the source byte for byte (SHA-256 `2270bf5db8aeebe5d3801d80aeeac94d9f7e8ab4c8640d73ddf01d6b65d3210c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
