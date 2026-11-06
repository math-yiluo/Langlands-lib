# Unitary regularity for actual Weil–Deligne Euler operators

This internal derived construction supplies the Euler regular-domain bridge for
an actual Weil–Deligne parameter whose underlying finite representation is
unitary. The group and carrier universes are independent and unrestricted. A
normal subgroup and an acting group element are supplied explicitly. The result
does not identify that element with local Frobenius or assert that an arbitrary
Weil–Deligne parameter is unitary.

The positive form is first pulled back along the published injective intertwiner
from the monodromy kernel, then along the published injective intertwiner from
its normal-subgroup invariants. Both inclusions are the actual subtype
inclusions. Thus the resulting form is invariant under the original group
operators on the actual inertia-fixed monodromy kernel. The auxiliary
`isUnitary_invariants`, `isUnitary_kernelRepresentation` and
`isUnitary_inertiaKernelRepresentation` lemmas state the corresponding
existential consequences.

The final lemmas apply the determinant regularity proved in
`Langlands.LocalFactor.UnitaryEuler` to precisely
`Langlands.LocalFactor.WeilDeligne.kernelOperator`. Consequently the published
Weil–Deligne Euler polynomial is nonzero when the polynomial variable has norm
different from one. At the published spectral variable `q^(-s)`, it is nonzero
for `q > 1` and `Re(s)` nonzero. `spectralRegularPointOfIsUnitary` constructs the
existing `SpectralRegularPoint` subtype without changing the parameter, its
action, its monodromy, its kernel, the subgroup or the spectral point.

The provenance is elementary restriction of positive definite invariant forms
through injective intertwiners, followed by the determinant kernel argument. No
new representation-theoretic source assertion is needed. This construction is a
prerequisite for arithmetic local-factor analysis; it does not prove the
associated-pair induction statement, positive-form existence for local
automorphic components, gamma comparison or any automorphic factor formula.
