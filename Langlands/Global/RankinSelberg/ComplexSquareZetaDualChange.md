# Changes of variables for the dual square zeta integral

`ComplexSquareZetaDualChangeStatement` gives the change of variables used to apply the upper-Borel square zeta computation to the dual side of Jacquet's equation (4.4). Left multiplication by the longest Weyl matrix preserves left Haar measure and its determinant has absolute value one. The test is pulled back by left multiplication by that matrix. The new vector sends `g` to `f(w₀(gᵀ)⁻¹)`. The change preserves both the integral and absolute integrability. `twistLin_mem_standard_ofFn` identifies the new vector's inducing characters as the inverses in reversed order.

`rightAverage_dual_change` makes the corresponding change of compact variable in the weighted Schwartz average. The automorphism `k ↦ (kᵀ)⁻¹` preserves compact Haar measure by Haar uniqueness at fixed total mass. Its composition with left translation by `w₀` is the involution used to twist the vector. The compact integral then has the original weight, and its matrix argument contains conjugation by `w₀` and right multiplication by `(kᵀ)⁻¹`.

`w0_conjugate_triangular` expresses that conjugation on triangular matrices in terms of transposition, reversal of the diagonal, and a permutation of strictly upper entries. `measurePreserving_reverseOff` proves that the permutation preserves products of identical sigma-finite measures, including the product of self-dual Haar measures.

These identities implement the dual change of variables in the Library's upper-Borel convention. [Jacquet, *Archimedean Rankin–Selberg integrals*, §4.7, equations (4.3)–(4.4)](https://doi.org/10.1090/conm/489/09547).
