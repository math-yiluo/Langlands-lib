# Elementary edge cases for the tempered exponent criterion

This is an internal statement interface supporting
`Langlands.GLTemperedExponentCriterionStatement`. It imports the published
criterion without changing it or its dependencies. It contains proposition
definitions, not proofs. The published theorem `Langlands.glTemperedExponentEdge`
(module [`TemperedExponentEdgeProof`](TemperedExponentEdgeProof.md)) proves
`GLTemperedExponentEdgeStatement`, and hence both clauses below.

`GLTemperedZeroCarrierStatement` quantifies over every supplied finite p-adic
field and topological realization, every rank (including zero), and every
complex representation on a subsingleton carrier. It asserts actual analytic
temperedness and the absence of every generalized Jacquet exponent for every
standard block shape. Temperedness retains its quantification over all Borel
Haar measures on the actual quotient by the center. Neither admissibility nor
a chosen central character is assumed in this clause.

`GLWeakExponentsUnitaryCentralCharacterStatement` assumes positive rank, a
nontrivial complex carrier, smoothness, and the scalar action of a supplied
character `ω : F.Carrierˣ →* ℂˣ`. Under the unchanged criterion's weak exponent
condition for every standard upper normalized Jacquet module and every
monotone block-absolute-value tuple, it asserts that `ω` has open kernel and
norm one everywhere. It also asserts existence of an actual
`UnitaryCentralCharacter ρ` on the full center, with its smoothness, norm and
scalar-action fields. Only smoothness is assumed here: finite-dimensional
fixed spaces are not needed for this elementary reduction.

`GLTemperedExponentEdgeStatement` is the conjunction of those two closed
propositions. The field and carrier universes `uF` and `uV` are independent.
The nontrivial-carrier hypothesis is confined to the second clause. In
particular, the interface does not assert that an arbitrarily supplied scalar
character on the zero representation is unitary.

## Derived provenance and proof outline

These are elementary reductions internal to the published definitions, rather
than translations of a separate theorem from the literature. No outside source
is claimed for this interface. The following outline was written before the
Lean proof, and `glTemperedExponentEdge` follows it.

For a zero carrier, all fixed-vector spaces are zero and hence finite, and
every vector is smooth. The trivial character of the full center supplies
unitary scalar action. Its matrix coefficients vanish, so their descended
norms belong to every required `L^(2+ε)` space. Each actual Jacquet quotient is
also a subsingleton, precluding the nonzero vector required by
`IsGeneralizedEigencharacter`.

For a nonzero carrier, a nonzero vector's open stabilizer and continuity of
the scalar embedding show that `ω` has open kernel. For the one-block standard
parabolic the unipotent subgroup is trivial and the normalizing modulus is
one. Its Jacquet module therefore retains a nonzero eigenvector for the
character obtained from `ω` by evaluating the sole block coordinate. Every
one-coordinate tuple is in the monotone chamber. Testing both a unit and its
inverse forces its character norm to equal one. Identifying the full center
of positive-rank `GL_n` with the scalar units then provides the required
`UnitaryCentralCharacter`.

These algebraic, topological and quotient identifications are proved in
`TemperedExponentEdgeProof`: its private lemmas `zeroCarrierClause` and
`unitaryCentralCharacterClause` prove the two clauses. Neither this statement
nor that proof supplies an asymptotic theorem, spectral decomposition,
coefficient bound, Haar-volume estimate or integrability argument for a
nonzero representation. The edge theorem alone therefore does not prove the
full tempered exponent criterion `GLTemperedExponentCriterionStatement`. That
criterion is proved separately by the published theorem
`Langlands.glTemperedExponentCriterion` (module
[`TemperedExponentProof`](TemperedExponentProof.md)), which uses
`glTemperedExponentEdge` for zero carriers and to construct the unitary
central-character datum. Some declarations in
`TemperedOppositeJacquetScalarLayerAssembly` and
`ProductLeviTemperedFactorizationAdapter` still take the criterion as an
explicit hypothesis (`hcrit`).
