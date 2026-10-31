# Actual covariants over full-group invariants

Author: Worker 94. This is an internal scalar-transfer construction from
`ArchimedeanCartanInvariantFiniteness` and `ArchimedeanCartanCovariants`.
It retains every number-field universe and every natural rank, including zero.

Write `R = lieSymmetricGroupInvariants K n` for the symmetric tensors fixed by
every element of the actual archimedean group and
`A = cartanSymmetricCompactInvariants K n` for the complementary symmetric
tensors fixed by every element of the actual full standard compact subgroup.
For `τ : ContinuousCompactRep K n`, write
`W = cartanSymmetricCovariants K n τ`. These are the fixed tensors in the
diagonal action on
`CartanSymmetricAlgebra K n ⊗[ℂ] (Fin τ.dim → ℂ)`.

`cartanGroupInvariantCompactAlgebra` equips `A` with its `R`-algebra structure
through the actual `cartanGroupInvariantRestriction`. This map is the actual
Cartan symmetric projection, restricted to full-group invariant tensors.
`cartanSymmetricCovariants_groupInvariantModule` restricts the existing
`A`-module structure on `W` along the same map. The two scalar identities state
that the action of `P : R` on `x : W` is the action of the restricted coefficient,
and that its underlying tensor is
`cartanSymmetricProjection K n P.val • x.val`. Multiplication acts on the
left tensor factor. `cartanSymmetricCovariants_groupInvariantTower` verifies
compatibility with the existing `A`-action.

`cartanSymmetricCovariants_groupInvariant_moduleFinite` proves that `W` is
finite as an `R`-module for this action. The implemented proof supplies
`cartanGroupInvariantRestriction_finite` as finiteness of `A` over `R`,
supplies `cartanSymmetricCovariants_moduleFinite` as finiteness of `W` over
`A`, and applies `Module.Finite.trans`. Both inputs concern the actual
coefficient algebras and actions constructed in the imported modules.

The result is algebraic finiteness of the actual symmetric covariants.
PBW, transfer to the enveloping center, admissibility, analytic density,
and the final automorphic differential-growth assertion remain separate
obligations.
