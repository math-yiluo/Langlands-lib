# Extending a split multiplicative-type fibre kernel to the base

Worker 879, using Worker 886's explicit character-restriction construction.
Internal derived interface in the kernel-factorization proof.

Let `S` be any scheme, `M` a finitely generated abelian group,
`f : D_S(M) → G` a homomorphism with separated target, and
`b : Spec k → S` any field-valued base morphism. The actual fibre kernel
is a closed subgroup of `D_k(M)`. Its compatible character model
supplies a surjection `M → N` and an isomorphism with `D_k(N)`
that preserves the inclusion. `fibreSubgroup f b` extends this
character group to `D_S(N)`, and `fibreSubgroupHom f b` extends the
surjection as a closed inclusion into `D_S(M)`.

`fibreSubgroupKernelIso` identifies the fibre of this extended subgroup
with the actual scheme-theoretic fibre kernel. The accompanying
inclusion equation proves equality of the full subgroup-functor ranges.
Consequently, the original homomorphism kills this extended subgroup
on the chosen fibre. No assertion that it kills the subgroup on a
neighborhood is made here; that is the subsequent rigidity step.

The implementation first compares base change of the integral
diagonalizable model with the actual group algebra over an affine
base. The comparison is natural for full-character restriction maps.
It then composes the compatible closed-subgroup model with the
published kernel-coordinate isomorphism. The inclusion equation
follows from naturality and the model's inclusion compatibility.
Point-functor ranges and triviality on the fibre follow from this
actual isomorphism, on every test scheme.

The character-restriction map and exact quotient construction are
unchanged same-task helper sources by Worker 886. All conclusions
are derived from these constructions and the published field
classification, full faithfulness and kernel base-change interfaces.
This module does not yet prove the relative kernel criterion.
