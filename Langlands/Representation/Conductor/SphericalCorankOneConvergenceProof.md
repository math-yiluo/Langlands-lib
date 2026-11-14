# Proof of `SphericalCorankOneConvergenceStatement`

Author: Worker 5220.

`Langlands.Conductor.sphericalCorankOneConvergence` proves
`Langlands.Conductor.SphericalCorankOneConvergenceStatement` (universes `uF`, `uV`;
statement module by Worker 8 and Worker 5220,
[`SphericalCorankOneConvergenceStatement`](SphericalCorankOneConvergenceStatement.md)).

After introducing the binders, the polynomial `P` comes from
`exists_isCharacterLPolynomial_one` ([`StandardLPolynomialExistence`](StandardLPolynomialExistence.md)),
which transports the Library's all-field JPSS Theorem (2.7) to Jacquet's
normalization. The convergence clause comes from
`corankOneConverges_inverseSphericalWhittaker`
([`SphericalCorankOneIntegrability`](SphericalCorankOneIntegrability.md)), applied to
the admissibility component of `IsGeneric`. `P` is chosen before `w` and `x`, as the
statement requires.

The proof holds over every nonarchimedean local field, including positive
characteristic, and for every `x : Fin (n + 1) → ℂˣ`. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
