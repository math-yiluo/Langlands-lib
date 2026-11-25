# Laurent presentations without related poles, and scaled poles

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ScaledPole`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file belongs to the degree-p, equal-characteristic step of eliminating ramification. For an Artin–Schreier parameter written as a Laurent expansion, b plus the sum of σ(cᵢ) π^(−(n−i)) over i < n, it normalizes the expansion so that no two "wild" coefficients sit at pole orders differing by a power of p, and it proves the arithmetic of scaled pole orders (n − i) p^(R − depthᵢ) that fixes the rank and depth of the orbit extension used later, uniformly for a finite family of data.

## Main results

- `exists_artinSchreier_presentation_with_smaller_support`: in an abstract setting (additive maps into a common group, a predicate P with P 0), if j ≠ j' both have coefficients failing P, and x and x^(p^r) represent the coefficient at j and its p^r-th power placed at j', replacing z by z plus the sum of x^(p^k) over k < r moves it there and strictly lowers the number of coefficients failing P.
- `exists_artinSchreier_laurent_presentation_without_related_poles`: if σ lifts a coefficient ring into B as a ring homomorphism modulo an ideal I ⊆ (π^n), any Laurent presentation can be replaced by one of the same shape, still generating M, in which distinct indices j, j' with coefficients failing P never satisfy n − j' = (n − j) p^r.
- `exists_unique_max_scaled_pole_of_le`: for a nonempty finite set J of indices below n with that separation property, depths, and any R at least n + 2 plus the sum of depthᵢ over i in J, some j ∈ J has the strictly largest scaled pole order; all exceed n, and the one at j is divisible by p.
- `exists_forall_unique_max_scaled_pole`: for a finite family of such data, one R serves every member, each with its own maximizing index.
- `exists_shared_orbit_parameters`: moreover one depth N ≥ 1 with n_c + 1 ≤ N for every member.
- `pow_mul_laurent_expansion`: π^n ξ = ∑ cᵢ π^i + π^n b.
- `exists_base_parameter_add_integral_of_coefficients_lift`: if the Laurent coefficients agree modulo π^n with elements of A, then ξ is an element of K plus an element of B.

Private lemmas give Artin–Schreier identities, a principal-part map and localization facts.
## Points to watch

- The docstrings stress that these results fix parameters only: none transfers a weak solution between data sets or asserts that one survives enlarging an extension, and the constant-parameter branch (pole order prime to p, coefficients from the residue field of A) is not addressed.
- The module docstring lists `exists_isGalois_totallyRamified_orbitExtension_forall_depth` among its four results, but that theorem is not declared in this file, nor is the variant with R equal to the bound that a docstring names.
- The bound on R is explicit but not meant to be sharp.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier/ScaledPole.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 21 declarations of the source file 20 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_unique_max_scaled_pole`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
