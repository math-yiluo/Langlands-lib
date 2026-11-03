# Existence of a maximal torus over the original field: statement

Worker 1336.

`MaximalTorusExistenceStatement.{u}` says that every smooth affine group
scheme `G` over any field `k : Type u` admits a commutative group scheme
`T` and a homomorphism `i : T.toGrp ⟶ G` satisfying the published
`IsMaximalTorus i`. In particular, `T` is a torus, `i` is a closed
subgroup, and every factorization through a larger closed torus has an
isomorphism as its factor map.

The torus and its embedding are over `k` itself. There is no assumption
that `k` is perfect or infinite, and no restriction on its
characteristic. Neither connectedness of `G` nor splitness of `T` is
required. The smooth affine hypotheses put `G` in the finite-type
algebraic-group setting: an affine morphism is quasi-compact, and a
smooth quasi-compact morphism over a field is of finite type.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 17.82 and Corollary 17.83,
printed p.379 (one-based PDF p.395, zero-based page 394). This is a
derived formulation of the rational existence input in the proof of
Corollary 17.83: choose a maximal torus over `k`, then apply Theorem
17.82 to obtain a maximal torus after extending the field. The displayed
Lean proposition retains the existence over `k` and does not itself
assert preservation of maximality under extension. Theorem 17.82
explicitly reduces to the identity component, so this source route
does not require the original group to be connected. The author's
registered errata snapshot of 2026-11-02 has no correction to these
two results.

This module only defines the proposition. It supplies no existence
proof, field-extension theorem, or proof that a torus maximal in a
parabolic is maximal in the ambient group. In particular, it does not
prove `ParabolicMaximalTorusStatement`. General maximal-torus
existence is a separate structural prerequisite of that task and of
the common-maximal-torus theorem for two parabolics.
