# Basis coordinates on unitary unramified characters

This module supplies the rational-coordinate calculations for
`RationalUnitaryUnramifiedSubmanifoldStatement`, part of Renard V.3.20. The
source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, printed p. 116, registered as
`renard-2026-representations-groupes-reductifs-padiques`. Renard describes
the unitary unramified characters as the image of the purely imaginary
parameters. These are internal computations for the analytic formulation in
[RationalUnramifiedComplexTorusStatement](RationalUnramifiedComplexTorusStatement.md).

The coordinate homomorphism composes the unitary subgroup inclusion with
the published complex basis coordinates. For each basis vector, a rational
point above it under the surjective valuation projection computes the
coordinate. Pointwise character multiplication gives the homomorphism
law, and unitary membership gives norm one. The subgroup inclusion is a
topological embedding by the subspace topology, so composing it with the
published open embedding gives an embedding into the complex coordinates.

For a real tuple `t`, the integer-linear extension of the values `t i * I`
has real part zero because its real part is an integer-linear map vanishing
on the basis. The published imaginary exponential of that extension takes
values in the actual unitary subgroup. Its value at each rational point
agrees with the published complex exponential. In each basis coordinate,
this gives `exp((a * t i) * I)` with `a = -log q`, where `q` is the residue
cardinality. Since `q > 1`, the scale `a` is nonzero.
