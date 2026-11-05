# Proof of first-order norm and trace character compatibility

This pair proves `padicDeepUnitNormTrace`, whose type is exactly the Library
proposition `PadicDeepUnitNormTraceStatement.{u,v}`, in independent universes.
Workers 84 and 27 are coauthors. Worker 27 supplied the integer
determinant/localization route, which survives in the public
`LocalClassField.quadraticNormTrace` and in the trace-integrality helper here.

## Trace integrality

The private helper `trace_mem_integers` shows that the field trace of an actual
integral `y` lies in the actual integer ring of `F`. It installs the published
relative integer scalar structures of `T` and `S`. It then uses
`NYLL.relativeIntegerStructure` to get that `S.Integers` is the integral closure
of `T.Integers` in `E` and is finite over it. Torsion-freeness follows from the
injective field map `F → E`, so `S.Integers` is free over the DVR `T.Integers`.
Since `F` and `E` are localizations of these rings, Mathlib's
`Algebra.trace_localization` identifies the field trace with the integer trace.

## Norm expansion and congruence

The proof imports the public `quadraticNormTrace` by its Lean name. It gives an
integral `r` with `N(1 + i(a) y) = 1 + a Tr(y) + a^2 r`, where `N` and `Tr` are
Mathlib's determinant norm `Algebra.norm F` and `Algebra.trace F`. All valuation
estimates use the supplied `T.discreteValuation`. Via
`mem_integers_iff_discreteValuation_le_one`, `a`, `Tr(y)` and `r` each have
valuation at most one. By the ultrametric inequality, `w = a Tr(y) + a^2 r` has
valuation at most `v(a)`, which is strictly below one. The strict
strong-triangle equality then gives `v(N(1 + i(a) y)) = 1`. This norm is
therefore nonzero, so by `Algebra.norm_ne_zero_iff` the element `1 + i(a) y` is
nonzero. It thus defines the required actual unit `z`, whose value is the
prescribed one by definition. Since `N(z) - 1 = w`, the bound
`v(a) ≤ exp(-n)` puts `Units.map (Algebra.norm F) z` in `T.principalUnits n`.
Both defining conditions of that subgroup are checked directly.

## Character computation and conductor

Applying the hypothesis on `χ` to this element of `T.principalUnits n` turns
the goal into an identity of values of `ψ` under `Circle.toUnits`. Expanding
`c (N(z) - 1) = c a Tr(y) + c a^2 r` and using additivity of `ψ` leaves the
error factor `ψ(c a^2 r)`. Its valuation is at most `v(c) v(a)^2`, which the
assumed bound places below `exp(T.additiveConductor ψ)`. So the error lies in
the actual additive-conductor lattice, and the first part of the published
`additiveConductor_spec` shows `ψ(c a^2 r) = 1`. What remains is
`ψ(c a Tr(y))`, which is the stated value.

## Topology and scope

The supplied topology `T.topology` forms the types of both characters. `ψ`
has type `UnitaryAdditiveCharacter F`, so it is continuous and nontrivial.
`χ` is a continuous homomorphism `F.Carrierˣ →ₜ* ℂˣ`. The proof uses the
topology through published inputs, not through a new topological argument:

- The actual conductor comes from `additiveConductor_spec`. That result is
  built in `Conductor` from the continuity of `ψ`, through the valuative
  neighborhood basis of zero in `F`, and from its nontriviality. The final
  step uses the conductor's first conjunct to kill `ψ(c a^2 r)`.
- The trace-integrality helper installs the supplied topologies, valuative
  relations and local-field structures of both `T` and `S`. With these, the
  integer rings get their algebra structures. `T.Integers` is a DVR and hence
  a PID through Mathlib's local-field instance, which uses local compactness.
  `NYLL.relativeIntegerStructure` gets integral closure and finiteness from
  the supplied normalization results `integers_finite` for `T` and `S` and
  `integers_isIntegralClosure` for `S`. The public `quadraticNormTrace`
  installs the same structures for its determinant expansion.

The final character computation does not use the continuity of `χ`. It also
proves no continuity statement for any map on `E`, such as the norm. It uses
only the prescribed values of `χ` on `T.principalUnits n`. The argument places
no condition on `p`, which may be two, or on the degree or ramification of
`E/F`. It also covers `n = 0` and `a = 0`, where `z = 1`.

This proof does not construct `χ`, and it does not prove finite order,
nontriviality, depth, trace transitivity or exact Galois stabilizers. Those
belong to the separate auxiliary-character assembly.
