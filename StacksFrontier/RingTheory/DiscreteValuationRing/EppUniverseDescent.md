# Transport of Epp’s hypotheses and finite extensions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseDescent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file gives the transport results needed to apply a common-universe form of Epp’s theorem to rings and fraction fields in independent universes. It also shows how to replace a finite field extension by an isomorphic copy in the universe of its base field.

- `isFractionRing_ulift` shows that a fraction field remains a fraction field after lifting both the domain and the field with `ULift`. `isExtension_ulift` carries the injective local maps that form extensions of discrete valuation rings to the lifted rings. The accompanying lemmas transport domains, discrete valuation rings, and scalar towers.
- `eppCondition_of_ringEquiv_square` transports Epp’s condition across a commuting square of ring isomorphisms between local ring extensions with local structure maps. The upper residue fields have the same exponential characteristic p. The condition says that every element of the upper perfect core is separable over the lower residue field. Auxiliary results transport characteristic, perfect-core membership, and separability across the induced residue isomorphisms.
- `integralClosureRingEquivOfSquare` gives a ring equivalence between integral closures when ring isomorphisms of the bases and ambient algebras commute with the structure maps. The equivalence acts by the ambient isomorphism on underlying elements.
- `exists_field_descent_of_module_finite` takes a finite extension E/K in any universe and gives a finite extension K₁/K in the universe of K, with a K-algebra isomorphism K₁ ≃ₐ[K] E.

Polynomial evaluation commutes with the isomorphisms, so monic witnesses to integrality and separable annihilating polynomials transport. The field descent embeds the algebraic extension E into the algebraic closure of K and takes its image. This works for inseparable finite extensions as well.

The comments cite Tag 09F9 and Tag 09II.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppUniverseDescent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
