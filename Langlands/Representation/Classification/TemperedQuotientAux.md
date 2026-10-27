# Algebraic adapters for the independent tempered quotient argument

This module is a small part of Worker 624's unfinished proof of
`Langlands.Classification.TemperedLanglandsQuotientCoverage`. It does not prove
coverage and does not assert any analytic, Jacquet-selection, induction-duality,
or tensor-duality input. Its internal provenance is the composition of the
published smooth-bidual constructions and reflexivity results with Mathlib's
irreducible-target criterion.

For representations `rho` and `sigma` of a topological group, a nonzero
intertwiner from the smooth dual of `rho` to `sigma` induces a pullback from the
smooth dual of `sigma` to the double smooth dual of `rho`. The first lemma
composes this pullback with the inverse of canonical bidual evaluation of
`rho`. If the composite vanished, every smooth functional on `sigma` would
annihilate the given intertwiner's image. Injectivity of `sigma`'s evaluation
map makes that image zero, contradicting the nonzero intertwiner. The resulting
map to the original `rho` is surjective because `rho` is irreducible.
`smoothDualPullbackToOriginal` defines this composite as an actual intertwining
map. `smoothDualPullbackToOriginal_surjective` proves the stated surjectivity
of that construction, and the existential wrapper returns that same map.

The compact-open-cofinal wrapper obtains separation for smooth `sigma` and
reflexivity for admissible `rho` from
`Smooth.Contragredient.AdmissibleDualityProof`. It requires no admissibility of
`sigma`, and it keeps the two carrier universes independent. The original
representation is the actual codomain of the surjection.

The final elementary lemma checks the exponent sign convention. Reversal on
`Fin r` reverses strict inequalities, and negation reverses them once more.
Thus a strictly decreasing exponent family remains strictly decreasing after
block reversal and negation, including for the empty index set.

No new literature claim is made. The nonzero-map and exponent arguments are
internal algebraic deductions. These lemmas do not establish the missing
prerequisites or the coverage theorem.
