# Representations attached to inertia types of finite period

Let `S` be a stage of degree `m + 1` between topological groups. Let `A` be an inertia
type whose class has minimal period `m + 1` under Frobenius conjugation. An inertia type
is a continuous irreducible representation on a finite-dimensional complex space
(`IsType`). Since `A` is irreducible, its carrier is nonzero
(`nontrivial_of_isIrreducible`). So the carrier hypotheses of `Irreducible` and
`Uniqueness` hold for the extension below.

`exists_stageRep` and `stageRep` choose an extension `τ` of `A` to the stage, using
`exists_extension` and `conj_equiv_of_minimalPeriod`. Its first block is
`A` (`block_stageRep`), its `k`th block is `A ∘ cj k` (`block_stageRep_eq`), and it is
continuous. Its blocks are irreducible and pairwise unrelated (`stageRep_hirr`,
`stageRep_hdist`).

`typeCoind S A hp` is the coinduction of this extension, on the carrier
`Fin (m + 1) → A`. Its properties:

- `typeCoind_isIrreducible` and `typeCoind_continuous`.
- `typeCoind_twist_iff`: the twist by the unramified character with parameter `u` is
  equivalent to `typeCoind` exactly when `u ^ (m + 1) = 1`. This combines
  `twist_equiv_of_pow_eq_one` and `pow_eq_one_of_twist_equiv`.
- `finrank_typeCoind`: its dimension is `(m + 1) · dim A`.
- `projType k`: the inertia intertwiner to the conjugate type `conjObj k A`. It is
  nonzero (`projType_ne_zero`).
- `twist_equiv_typeCoind`: let `σ'` be an irreducible representation of `G` on a
  finite-dimensional complex space `V'` (`[FiniteDimensional ℂ V']`), with a nonzero
  inertia intertwiner from `σ'` restricted to inertia to `A`. Then some unramified twist
  of `σ'` is equivalent to `typeCoind` (from `twist_equiv_coind_of_occurs`).
- `occurs_typeCoind`: every type `B` receiving a nonzero inertia intertwiner from
  `typeCoind` has class `conjType k [A]` for some `k < m + 1` (from `exists_block_equiv`).
- `typeCoind_trivial_iff`: for a normal subgroup `N`, `typeCoind` is trivial on the
  inertia elements of `N` exactly when `A` is (from `coind_trivial_iff`).

For any representation `τ` of the stage, on any complex vector space (no finiteness is
needed here):

- `blockConjEquiv` gives the equivalence between its first block and the conjugate of
  that block by `lift ^ (m + 1)`, via `τ(E.lift)`.
- `block_isIrreducible`: the first block is irreducible when the restriction of `τ` to
  stage inertia is.

This module packages the Clifford-theoretic classification used in Henniart (1988),
Proposition 2.2, for internal use in the unramified-descent count.
