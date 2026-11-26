# Henniart's numerical correspondence in rank one

For every p-adic field \(K\), `rankOneNumericalEquiv` equips the geometric
reciprocity bijection with the conditions of `Numerical.IsNumericalInjection`
in rank one. The Weil and supercuspidal carrier universes are independent.
`rankOneNumericalInjection_surjective` proves that every map meeting those
conditions in rank one is surjective.

The Artin conductor of the Weil character pulled back by reciprocity is the
multiplicative conductor of the field character, by
[`rankOne_hasArtinConductor_iff`](HenniartWeilRankOneCountProof.md).
On the group side, the lifted scalar representation has first fixed level
equal to the same multiplicative conductor by
`Conductor.firstFixedLevel_eq_multiplicativeConductor`. Geometric reciprocity
identifies Weil degree with the valuation of the image, so twisting by
\(z^{\operatorname{ord}_K}\) on \(K^\times\) induces the numerical twist by
\(z\) on each side. `rankOneReciprocityEquiv_twist` gives the resulting
identity on the actual rank-one classes.

The proof of `rankOneCountsAgreeUpToSlope` chooses a geometric reciprocity map
by `LocalClassField.weilReciprocityTheorems`. It applies the counting direction
of [`refinedStrata`](HenniartRefinedStrataProof.md) at rank bound \(1\), using
the reciprocity bijection and `weilArtinConductorExistence`. This gives equal
finite refined orbit counts for every real slope bound. For any target
supercuspidal class of rank one, write it as a field character and take the
slope bound to be its multiplicative conductor minus one, with subtraction
in the natural numbers. The surjectivity direction of `refinedStrata` at that
bound places the class in the range of the given numerical injection.

Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
Ann. Sci. Éc. Norm. Sup. (4) 21 (1988), §1.2 and Théorème 1.2, printed
pp. 497–498, specifies geometric reciprocity in rank one and the numerical
injection and surjectivity conditions. The Lean proof uses the comparison
with refined orbit counts in rank one
(`henniart-1988-numerical`,
SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`).
