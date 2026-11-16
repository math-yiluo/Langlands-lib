# An actual root with the E₈ highest-root coefficients

This internal derived unit constructs an actual root with integral
coefficients `(2, 3, 4, 6, 5, 4, 3, 2)` in any selected family of eight roots
whose Cartan pairings equal Mathlib's numbered E₈ matrix. It does not require
linear independence of that family. The conclusion asserts existence of this
root, without asserting maximality among the positive roots.

The proof starts with the eighth selected root, whose coefficient vector is
`(0, 0, 0, 0, 0, 0, 0, 1)`, and applies the coefficient reflection theorem
from `RootReflectionCoefficients` at the vertices

`6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7`.

Each intermediate coefficient vector and each reflection equality is explicit
in the Lean proof. Ordinary kernel-checked `decide` verifies the integer
arithmetic. Root-datum reflection closure realizes every step as an actual
root. This explicit certificate uses no external classification theorem.
