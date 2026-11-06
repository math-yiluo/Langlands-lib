# Invariant subspaces of actual additive-group representations

Let `k : Type u` be a field, let `n : Type` be a finite decidable coordinate
type, and let `ρ` be an actual matrix representation of the one-dimensional
vector-group scheme over `k`. The module constructs its coefficient orbit
subspaces and compares coefficient invariance with the existing
`MatrixRepresentation.IsStableSubspace`, which quantifies over every
commutative test algebra and every ground-field linear functional on that
algebra. The field may be finite, and the test algebras may be nonreduced.
The coordinate type may be empty except in the final nonzero-existence result.

`affineAction_eq_aeval_polynomialOrbit` identifies the actual affine action
at scalar `t` with evaluation at `t` of the universal polynomial orbit from
`AdditiveFixedVectors`. This follows by the existing comparison between the
univariate matrix and the actual affine matrix, and by commuting evaluation
with the finite matrix-vector sum.

`polynomialOrbit_eq_sum` chooses one bound, one more than the maximum of the
coordinate polynomial degrees. Every coordinate is then the finite sum of
its actual divided-power coefficients times powers of the variable.
`linearFunctional_affineAction_eq_sum` evaluates this expansion and applies
an arbitrary linear functional `ℓ : A →ₗ[k] k`. The resulting vector is

`∑ m ∈ Finset.range N, ℓ(t ^ m) • dividedPower ρ m v`.

The bound depends on `v` and `ρ` and works for every test algebra, scalar
and functional. The calculation uses linearity of `ℓ` over `k`, without
requiring multiplicativity.

`isStableSubspace_iff_invariant_dividedPower` says that a subspace `W`
is stable in the published all-test-algebra sense if and only if
`dividedPower ρ m v ∈ W` for every natural number `m` and every `v ∈ W`.
For the forward implication, the test algebra is `k[X]`, the point is the
universal scalar `X`, and the functional extracts coefficient `m`.
For the reverse implication, every affine additive-group point is represented
by its single scalar coordinate. The preceding finite expansion expresses
each linear coefficient of its action as a linear combination in `W`.
Thus coefficient recovery here uses the universal algebra rather than
an infinitude hypothesis on the base field.

`orbitSubmodule ρ v` is the linear span of the vectors `dividedPower ρ m v`
for all `m`. It contains `v` because the zeroth coefficient is the identity.
The divided-power composition law makes every coefficient operator preserve
this span: applying `D_m` to `D_a v` is the scalar
`choose(m+a,m)` times `D_(m+a) v`. The stability equivalence then proves
`isStableSubspace_orbitSubmodule`.
For any stable `W`, `orbitSubmodule_le_iff` identifies containment of the
orbit submodule in `W` with membership of `v` in `W`. This is its least
stable-subspace property.

If `p` is prime and `CharP k p`, the existing
`invariant_dividedPower_iff_invariant_pPowerOperator` reduces the stability
criterion to invariance under the operators at degrees `p^r`.
`isStableSubspace_iff_invariant_pPowerOperator` gives this criterion over
all test algebras, retaining no infinite-field assumption.

`mem_fixedSubmodule_iff_isFixedVector` identifies the coefficient common
kernel from `AdditiveFixedVectors` with the canonical
`MatrixRepresentation.IsFixedVector`, whose definition tests arbitrary
relative schemes. A canonical fixed vector is fixed on affine tests.
Conversely, coefficient fixedness gives fixedness at the actual affine model
of the vector group, and the existing `isFixedVector_iff_affine_model` pulls
this equation back along every relative scheme point.
`fixedSubmodule_eq` records equality with the canonical fixed submodule.
In prime characteristic, `isFixedVector_iff_pPowerOperator` consequently
identifies canonical all-scheme fixedness with the common `p`-power kernels.
With nonempty coordinates, `exists_nonzero_isFixedVector` transports the
predecessor's nonzero coefficient-kernel vector through this identification.
Nonzero fixed-vector existence alone is already implied by the published
unipotence of vector groups; the additions here are the actual operator and
subspace comparisons.

This is a derived prerequisite. Its proofs use the actual coefficient
construction and divided-power law, finite polynomial expansion, the
published stability predicate, and the existing affine-model detector.
The supplied representation is not constructed here. No root subgroup,
highest-weight or Steinberg representation, irreducibility, or general
big-cell existence is asserted, and `SteinbergBigCellStatement` remains
a separate proof obligation.
