# Cuspidal `L²` under the adelic Weil comparison

The positive rational quotient homeomorphism identifies the full almost-everywhere cuspidal spaces by pullback. The equivalence preserves the classes of pulled-back functions and intertwines right translation for the two adelic groups.

For corresponding proper parabolics, the two integrands agree on representatives by the homomorphism law, which identifies the translated radical points. `measurePreserving_weilRadicalQuotient` then gives equality of periods and equivalence of integrability. The norm-one Haar comparison transfers both almost-everywhere conditions since its scalar is positive. The two parabolic matching theorems supply the universal quantifiers in both directions.

`MeasureTransport.l2Equiv` gives the ambient continuous linear equivalence for the proportional quotient measures. The almost-everywhere congruence theorem `mem_aeParabolicCuspidalFunctionSubmodule_congr` lets the pointwise calculation apply to representatives of `Lp` classes. The restricted equivalence intertwines the bounded actions by the right-translation identity on the quotient and the almost-everywhere formulas for composition.

`cuspidalEquiv_irreducibleSummand` carries a nonzero closed invariant submodule with no proper nonzero closed invariant submodule to one with the same properties. The proof pulls back closed invariant submodules by the inverse linear equivalence and uses surjectivity of the adelic comparison for invariance under every group element. `topologicalClosure_range_comp_equiv` identifies the closure of a transported linear range by taking the inverse image under the inverse homeomorphism.

The proof composes the Library's normalized parabolic period construction with the Weil point and norm-one comparisons. The mathematical inputs for those comparisons are detailed in `AdelicWeilPositiveQuotient` and `GroupSchemeWeilParabolicTransport`.
