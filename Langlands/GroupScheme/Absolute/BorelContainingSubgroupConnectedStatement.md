# Connectedness of a smooth closed subgroup containing a Borel: statement

Worker 1336.

`BorelContainingSubgroupConnectedStatement.{u}` concerns a smooth affine
group scheme `G` with connected underlying space over an algebraically
closed field `k : Type u`. Let `i : P ⟶ G` be an actual closed subgroup
whose structure morphism is smooth. If a Borel subgroup `j : B ⟶ G`
has a factor `f : B ⟶ P` satisfying `f ≫ i = j`, then the underlying
space of `P` is connected.

The conclusion is `ConnectedSpace P.X.left`. No connectedness of `P`
is assumed. There is no reductivity, splitness, or characteristic
restriction. Closedness is the published `IsClosedSubgroup`, which
means that the underlying scheme morphism is a closed immersion.
Smoothness of `P` is explicit, and its closed immersion into affine
`G` puts it in the finite-type affine group-variety setting.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Corollary 17.49 and its proof, printed
p.367 (one-based PDF p.383, zero-based page 382). The corollary asserts
connectedness and self-normalization for a subgroup variety containing
a Borel. This derived proposition retains only connectedness over an
algebraically closed field and replaces identified subgroup containment
by the actual factorization equation. Its ambient group is connected,
as in the source section. The source proof compares the identity
component with the subgroup normalizer using conjugacy of Borels and
the Borel normalizer theorem. The registered author errata snapshot of
2026-11-02 has no correction to Corollary 17.49.

This module only defines a proposition. It supplies no connectedness
proof or normalizer theorem. Applying it after extension to an
algebraic closure is a geometric step in the source derivation of
`ParabolicMaximalTorusStatement`; that derivation still requires the
other structural prerequisites and an actual proof.
