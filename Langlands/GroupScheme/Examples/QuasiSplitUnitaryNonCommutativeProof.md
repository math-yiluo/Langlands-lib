# Noncommuting rational points of the hyperbolic unitary group

Author: Worker 1150.

`Langlands.GroupScheme.QuasiSplitUnitary.nonCommutative` proves exactly the
published proposition `NonCommutativeStatement.{u}`. It retains the arbitrary
universe, fields, quadratic extension, finite basis and nonidentity algebra
automorphism in that statement, without a characteristic restriction.

This proof is an internal, derived matrix calculation. It uses the published
`QuasiSplitUnitary` model and point equivalence, and the trace-zero parameter
space and upper root map in `QuasiSplitUnitaryDynamic`. It does not assert a
new literature theorem or require any additional source beyond those Library
interfaces.

The proof takes the test scheme to be the terminal object over `Spec F` and
writes `R` for its global-sections algebra. The isomorphism
`Scheme.ΓSpecIso` identifies its underlying ring with `F`, so `R` is nonzero.
Since `c` is not the identity, some `t` satisfies `c(t) ≠ t`. Set
`x = (t - c(t)) ⊗ 1` in `E ⊗[F] R`. The map `e ↦ e ⊗ 1` is injective:
`F → R` is injective because `F` is a field and `R` is nonzero, and tensoring
with the flat `F`-module `E` preserves injectivity. The implementation uses
Mathlib's `Algebra.TensorProduct.includeLeft_injective`. Thus `x ≠ 0`.
The published identity `c(c(t)) = t` gives `x + c_R(x) = 0`, so `x` belongs
to `traceZero R c`.

Write `J = [[0,1],[1,0]]`. Direct entry calculations establish `J² = 1`,
package `J` as an invertible matrix and verify its membership in
`matrixPoints R c`. The second matrix is the published upper root element
`u(x) = [[1,x],[0,1]]`; its trace-zero parameter ensures membership in the
same unitary subgroup. The products have entries
`(J u(x))₀₀ = 0` and `(u(x) J)₀₀ = x`. Equality of the products would
contradict `x ≠ 0`.

Finally, the multiplicative equivalence `pointsEquiv b c T` transports these
two matrices to actual morphisms from the terminal test scheme to
`(groupScheme b c).X`. Applying the equivalence to a hypothetical equality
of their products yields the matrix equality just ruled out. No division by
two occurs, so the argument also applies in characteristic two.
