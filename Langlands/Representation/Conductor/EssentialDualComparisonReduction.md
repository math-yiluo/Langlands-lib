# Algebraic reduction for the dual comparison

Author: Worker 106.

This is an internal, derived interface for the proof of the published
`Langlands.Conductor.EssentialDualComparisonStatement`. It supplies no
unconditional dual comparison or functional equation.

The model map `dualComparisonModelMap` is the published `firstDualModelMap`,
transported to an arbitrary functional whose value is the prescribed dual
functional. Its pointwise value is the published `dualFunction`.

Mirabolic restriction injectivity promotes integral Levi invariance from the
Levi slice to the full group: the translated and original model vectors have
equal Levi restrictions, hence equal mirabolic restrictions, hence are equal.
Inverse transpose preserves the integral subgroup and commutes with rank
inclusion; the latter uses the published
`Langlands.RankinSelberg.HighlyRamified.inverseTranspose_rankInclusion`. Applying these identities shows that the actual dual function is
also integral invariant on its restriction. A right scalar translation in the
smaller Levi preserves restriction invariance by commutation with integral
matrices.

The lemma `eq_smul_of_unit_spherical_integrals` compares two invariant model
vectors `u` and `v`. If their absolutely convergent corank-one integrals are
proportional with constant `C` on a real half-line for every unitary Satake
parameter, the vector `u - C • v` is restriction invariant and its integrals
vanish. The imported unitary separation theorem makes its mirabolic restriction
zero, and the explicitly supplied mirabolic injectivity then makes the vector
zero on the full group.

The final lemma `dualComparison_of_unit_spherical_integrals` applies this
comparison in the inverse-transpose model to the dual of `w` and the right
translate of `w'` by `diag(ϖ^m, ..., ϖ^m, 1)`. It assumes restriction invariance
of `w` and `w'`, smoothness, mirabolic injectivity in both models, and the
proportionality of these spherical integrals. It concludes the pointwise
identity of JPSS (5.3), printed page 213. The proportionality is an explicit
remaining analytic input; this lemma does not prove the published
`EssentialDualComparisonStatement`.

All these are algebraic consequences of the imported model constructions and
the explicitly supplied restriction injectivity. No existence of essential
vectors, conductor theorem, or functional equation is assumed as an established
result. The field and vector-space universes are independent.
