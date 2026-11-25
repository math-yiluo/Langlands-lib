# Coefficient descent and Artin–Schreier shifts in mixed characteristic

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.ArtinSchreierShift`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file descends the scaled parameter of a prepared cyclotomic quotient equation to the base modulo a uniformizer power. It also gives a level bound after an Artin–Schreier shift and a splitting criterion for the tensor product of a Galois layer.

- `exists_scaled_parameter_eq_of_mapped_dvr_preparation` takes weakly unramified maps A → B and B₀ → B, a uniformizer π of A, and a perfect residue field of A of characteristic p. A prepared polynomial over B₀ of degree at most n lifts a residue polynomial H₀ modulo the mth power of the maximal ideal, where m > 0 and p vanishes in this quotient. If πⁿξ agrees modulo πᵐB with πⁿ times the mapped polynomial evaluated at π⁻¹, then πⁿξ is congruent to an element of A modulo πᵐB.
- `finiteLevel_tensorProduct_of_artinSchreier_shift` starts with a degree-p layer M/L and a cyclotomic quotient equation P(z) = ξ over the discrete valuation ring B of L, with z generating M over L (`hz`) and P any polynomial for which `hP` gives `intProp`, `quotChar`, `shapeProp` and `funcEq`. Write e for the valuation of w = 1 − ζₚ, and suppose πⁿξ ≡ a modulo πᵐ. If a further base change makes the two tensor products fields and supplies y with πⁿ(yᵖ − y) = −a, the new layer has finite level at most (n − m)/e. The bound uses n < pe, m ≤ e, m ≤ n and n + m ≤ pe.
- `exists_tensorProduct_pi_algEquiv_of_embedding` takes a finite Galois extension M/L with a generator and an L-embedding of M into the field L ⊗ₖ E. It splits M ⊗ₖ E into copies of L ⊗ₖ E indexed by the Galois automorphisms. Supporting lemmas preserve degree and generation under tensoring and transfer the shift equation along the right tensor inclusion.

For descent, the chosen lifts agree on the perfect core by uniqueness modulo a nilpotent ideal. The level bound comes from replacing z by (1 + wy)z + y and estimating the cyclotomic quotient error by valuation. Splitting uses linear independence of the conjugate embeddings and a dimension count.

The descent premises `hcore` and `habs` require perfect-core coefficients and their absorption into the base residue image. The shift theorem takes fieldness `hL`, `hM` and the discrete valuation ring and fraction-field properties `hB`, `hfrac` of the integral closure as inputs. Its field and ring types share a universe.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/ArtinSchreierShift.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 17 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.EppLevelInduction.isField_iff_irreducible_minpoly_of_adjoin_eq_top`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
