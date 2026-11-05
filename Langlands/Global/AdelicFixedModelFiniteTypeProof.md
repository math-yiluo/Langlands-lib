# Proof of finite-type arithmetic fixed-model comparisons

The theorem `adelicFixedModelFiniteType` proves exactly
`AdelicFixedModelFiniteTypeStatement`. In each arithmetic branch, install the
Noetherian ring instance proved for the actual initial integer ring by
`adelicSIntegersNoetherian`. Mathlib's spectrum instance makes the base
locally Noetherian, and its morphism instance upgrades the model's local
finite type to local finite presentation. Apply the locally finitely
presented clause of `adelicFixedModelPointComparison` unchanged.

That clause gives exactly stage factorization, bijectivity and the
homeomorphism assertion for the specified canonical comparison and two
final topologies. The implementation preserves the function-field
presentation and scalar tower needed for curve integer Noetherianity,
every infinite number-field factor, empty initial finite sets, arbitrary
nonaffine models and arbitrary common universe. Quasi-compactness is kept
in the target to match the source's finite-type models; it is not needed
by the local finite-presentation deduction. The proof asserts no further
generic-fiber or model-independence result.
