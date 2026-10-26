# Algebraic-to-closed irreducibility in an admissible Hilbert realization

Authors: Worker 386 and Worker 340.

The proposition definition
`Langlands.AdmissibleAlgebraicToClosedIrreducibilityStatement.{uG,uV,uH}`
states an internal comparison for an admissible algebraically irreducible
complex representation and its actual dense Hilbert realization. This file
states the proposition and supplies no proof.

## Exact scope

The three universes are independent. The group `G` is a topological group,
with compact open subgroups cofinal among open subgroups: for every
`K : OpenSubgroup G`, some compact `L : OpenSubgroup G` satisfies `L ≤ K`.

The carrier `V` is an algebraic complex module. Its actual representation
`ρ : Representation ℂ G V` is admissible in the existing Library sense:
every vector is fixed by an open subgroup, and every open subgroup has a
finite-dimensional fixed space. The existing predicate
`Representation.IsIrreducible ρ` requires a nonzero carrier and no proper
nonzero algebraic invariant submodule. The data include an actual invariant
positive definite Hermitian form `b : Langlands.InvariantPositiveForm ρ`.
The original carrier has no specified norm or topology.

The target `H` is a complete complex normed inner-product space. The actual
action `π : G →* (H →L[ℂ] H)` consists of continuous complex-linear operators.
The actual complex-linear map `j : V →ₗ[ℂ] H` must have dense range,
intertwine the given actions, and satisfy the exact pullback identity

```text
inner ℂ (j v) (j w) = b.inner v w.
```

Positive definiteness implies that `j` is injective. Equivariance and the
pullback identity imply that `π(g)` preserves the inner product on pairs
in the dense image; continuity extends that identity to all target vectors.
These are consequences of the premises, rather than additional premises.
Joint continuity or continuity of the orbit maps in the group variable is
not required. Neither carrier is assumed finite-dimensional.

The conclusion is the existing
`Langlands.Archimedean.IsTopologicallyIrreducible π`: the carrier `H` is
nonzero, and every closed complex submodule invariant under all `π(g)` is
bottom or top. Despite its namespace, this predicate has no Lie-group,
manifold or differentiability assumptions. It concerns closed subspaces
of `H`; the hypothesis on `ρ` concerns every algebraic invariant subspace
of `V`.

## Internal provenance and proposed proof

This is an internal derived comparison, with no attribution to an external
theorem. Its intended proof uses the existing admissible smooth-vector
recovery proposition and the standard orthogonal projection in Mathlib.
The recovery statement and its proof are in the separate modules
`Langlands.Representation.Unitary.SmoothVectorRecoveryStatement` and
`Langlands.Representation.Unitary.SmoothVectorRecoveryProof`. The present
module imports neither proof nor comparison certificate.

For a closed invariant subspace `W` of `H`, completeness provides the
orthogonal projection `P` onto `W`. Inner-product invariance makes the
orthogonal complement invariant as well, so `P` commutes with every action
operator. Each `P(j(v))` is therefore fixed by an open subgroup fixing `v`.
The proposed recovery theorem identifies it with `j(v')` for an actual
source vector `v'`.

The inverse image of `W` under `j` is an algebraic invariant subspace of
`V`. If it is the whole source, density of `j` and closedness of `W`
give `W = H`. If it is zero, the recovered preimages of `P(j(v))` vanish,
so `P` vanishes on the dense image. Continuity then gives `P = 0`,
and hence `W = 0`. Injectivity and the nonzero source give a nonzero target.
This paragraph explains a proposed route and the explicit completeness
premise; it is not an implemented Lean proof.

The opposite implication, from closed irreducibility to algebraic
irreducibility, is a separate comparison. This proposition constructs
no Hilbert completion, central-character L2 space, coefficient embedding,
induction model, Mackey decomposition or Whittaker functional.
