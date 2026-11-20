# Strict positivity of the canonical opposite-intertwiner scalar

`Langlands.Plancherel.conditionalDynamicOppositeUnitaryPositive` proves
`ConditionalDynamicOppositeUnitaryPositiveStatement.{u, uV}`. The canonical
composition scalar `j_P` is nonzero in the rational function field. At every
unitary unramified character in `p.regularRegion ∩ q.regularRegion`, both
`j_P` and `j_P⁻¹` are regular with positive real values.
[Published target](DynamicOppositeUniformNonvanishing.md)

The theorem applies `conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction`
to the published `conditionalDynamicOppositeHermitianAdjunction`. In the
reduction, a nonzero inducing vector `v` gives a compact-picture test vector
`e` whose forward image has value `c • v` at the identity for a fixed `c ≠ 0`
throughout the forward convergence domain. The identity principle extends this
evaluation to the selected forward regular region. Thus the squared-norm
quotient from the continued Hermitian adjunction is strictly positive at each
unitary common regular point. The reduction chooses a unitary character at
which both continuation denominators are nonzero to deduce `j_P ≠ 0`. At each
such point, interchanging the numerator and denominator of a presentation
gives regularity and positivity of `j_P⁻¹`.
[Reduction](DynamicOppositeUniformNonvanishing.md)
[Hermitian adjunction](DynamicOppositeHermitianAdjunctionProof.md)

The type retains the structural premises, both compact factorizations and
Levi splittings, unitarizability, the continuation data, the nonempty open
convergence sets, generic irreducibility and `_hdag`. The latter supplies
reverse convergence at the conjugate inverse of each point of the forward
open set. The field and representation carrier universes are independent.

The uniform test-vector step comes from IV.1 (10) and the adjunction from
IV.1 (11), printed p. 283 (PDF p. 49). The squared-norm step comes from the
proof of IV.3 (6), printed p. 287 (PDF p. 53). The Library's derived result
uses the test vector directly on the common regular region. The source is
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered
as `waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[Original article](https://doi.org/10.1017/S1474748003000082)

Worker 228, Task 7228.
