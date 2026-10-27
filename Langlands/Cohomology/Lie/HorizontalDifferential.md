# Horizontal stability of the coefficient differential

This internal unit derives horizontal stability from the existing actual
Chevalley–Eilenberg coefficient differential and its evaluation formulas.
It does not introduce a supplied differential. Its final linear map restricts
that differential to the actual intersection of horizontal and full-group
equivariant alternating cochains.

The scalar field `K` has characteristic zero. The Lie algebra `L`, coefficient
Lie module `M`, and, in the full-group construction, group `G`, have independent
universes. No dimension or topology assumption is imposed. A submodule
`H : Submodule K L` specifies the horizontal directions; bracket closure of
`H` is not required for the conditional stability result.

For a degree-`q` cochain `f` that vanishes whenever any argument belongs to
`H`, `differential_cons_of_horizontal` proves

```text
(d f)(y, x) = [y, f(x)] - sum_i f(update x i [y, x_i])    (y in H).
```

In positive degree, all action summands other than the first vanish by
horizontality. Among the bracket summands, those with neither index zero
retain `y` as an argument and vanish for the same reason. The remaining
bracket-first summands move their first argument back to its original slot:
alternation contributes `(-1)^i`, canceling the index-dependent sign and
leaving the negative insertion sum. In degree zero the sum is empty and
the formula is the existing coefficient-action formula.

`differential_mem_horizontal` assumes additionally, for this cochain,

```text
[y, f(x)] = sum_i f(update x i [y, x_i])    (y in H).
```

The preceding identity gives zero when a horizontal direction is first.
The alternating-map insertion formula moves a direction in any slot to the
first slot, proving that the actual differential is horizontal in every slot.
All natural degrees, including zero, are covered.

For actual group representations `sigma` on `L` and `rho` on `M`, suppose
`sigma` preserves brackets and the actions satisfy
`rho(g)[x,m] = [sigma(g)x,rho(g)m]`. The construction
`horizontalEquivariantDifferential` also takes the explicit hypothesis that
every cochain in the degree-`q` horizontal full-group-equivariant intersection
satisfies the displayed infinitesimal insertion identity. It sends `f` to
the existing `differential q f.val`. Horizontal membership follows from the
new theorem; full-group equivariance follows from the published
`differential_mem_equivariant`. Linearity is inherited from the differential,
and `horizontalEquivariantDifferential_val` records its exact underlying map.

The infinitesimal hypothesis is explicit generic input, not a consequence
of arbitrary algebraic group representations. An application to actual
automorphic coefficients must discharge it by the proved compact
differentiation theorem and must prove covariance of its actual coefficient
action. This module does not attach those actions or assert square zero,
construct cycles, boundaries or cohomology, or identify any external
cohomology theory.

The provenance is internal. The differential, its signs and its increasing
deletion and bracket-first formulas are imported from
`CoefficientCochains`. Full-group stability is imported from
`CoefficientFunctoriality`. Horizontality and the full-group intersection
are the exact submodules in `HorizontalAlternating`. The only additional
combinatorics are Mathlib's alternating-map insertion formula and finite
tuple and sum identities. No new external-source identification is asserted.

Authorship: Worker 2.
