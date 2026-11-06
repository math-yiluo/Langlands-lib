# Selected weights on the actual Levi Jacquet module

This internal adapter is motivated by the passage to unitary parts in Renard
2026, VII.2.5 (printed p.230 / PDF p.236), with the compact-open characteristic
spaces of VII.1.1 (printed p.220 / PDF p.226) and the unitary part of VII.2.3
(printed p.229 / PDF p.235). It compares two published models of the same
subspace; it does not establish the geometric lemma or its tempered analogue.

`leviJacquetWeightSpace_toSubmodule` compares the generalized weight space of
the Jacquet module transported to the actual group `M(F)`, using the central
map `rationalPoints.map a`, with the normalized Jacquet weight space defined
on the literal Levi image in `G(F)`. Both models are smooth. Their compact-open
membership conditions therefore reduce to the uniform generalized-eigenvector
condition. The action through `leviPointsEquiv` agrees with the literal
split-component point map, and the same power works for every element on
both sides. The equality is an equality of actual underlying submodules.

`selectedWeightPart_leviJacquet_toSubmodule` sums these equalities over the
characters whose normalized real part is zero. The published
`unitaryJacquetPart_eq_iSup` removes the redundant exponent condition on the
unitary-part side.

`selectedLeviJacquetEquivUnitary` uses the resulting equality of submodules
to give an actual equivariant linear equivalence from the selected part of
the Levi Jacquet representation to `leviUnitaryJacquetModule`. Its forward
map is the identity on ambient vectors, as the application lemma states.
The Levi has its published canonical point topology and the transported
local compactness and nonarchimedean-group instances. No admissibility or
temperedness hypothesis is needed for these comparisons.
