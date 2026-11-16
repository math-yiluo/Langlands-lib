# Exact central integral images

Waldspurger 2003, VIII.4, printed p.327, defines
`pχ(f)(g) = ∫ a ∈ A_G, χ(a)⁻¹ f(a g) da` and asserts absolute
convergence. Proposition VIII.4.1 and Theorem VIII.4.2 concern its
images of the cuspidal Schwartz space and its levels. The registered
source is `waldspurger-2003-plancherel`,
DOI 10.1017/S1474748003000082.

This unit constructs these exact raw images as sets using the published
`centralProjection` integral. `schwartzCentralIntegralImage E muA χ`
means that an actual `φ ∈ E` has precisely the given integral function.
It assumes no convergence theorem. Because Lean's Bochner integral is
totalized, that set is not silently asserted to be a submodule.
`schwartzCentralIntegralSpan` is explicitly its complex span.

`CentralIntegralConvergesOn` states absolute integrability at every
group argument for every input in `E`.
Given this analytic property, `centralIntegralOn` is the actual integral
as a linear map on `E`; its addition law uses `integral_add` only after
convergence has been supplied. The proved range and span comparisons
show that the span equals the exact image. This is an auxiliary generic
implication, not an unconditional analytic convergence theorem.

The published `CentralWeights` and measurable unitary character supply
this convergence through `CentralWeights.convergesOn`.
`schwartzCentralIntegralSpan_eq_map` identifies the span with the
published `Space.centralProjection` image. These weight assumptions
are exposed only in the auxiliary comparison.

The rational-point abbreviations specialize to the constructed actual
`rationalCuspidalSubmodule`, its bi-invariant levels `°C_H`, and its
left-invariant levels `°C(H \ G)`. The central subgroup is literally
`(rationalPoints.map s).range`; for a split component `s` this is
`A_G(F)`. The raw integral images, spans, level inclusion and level
refinement are constructed without estimates.
`rationalCuspidalCentralImage_eq_map` and its level counterpart compare
them with the exact image of the published `rationalCentralProjection`
under explicit `CentralWeights`.

The field, group, canonical rational-point topology, chosen torus,
cocharacter, compact open subgroup and its Iwasawa pair, matrix height,
central subgroup, measure and character remain visible. The construction
does not assume a particular characteristic, splitness or quasi-splitness.
The later closed targets impose connected reductivity, a split component,
Haar measure and continuous unitary character and place convergence
in conclusions, without taking the weights as premises.
