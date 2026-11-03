# Preservation of unipotence under field extension

Author: Worker 1473.

`Langlands.GroupScheme.UnipotentFieldExtensionStatement.{u}` states the
forward implication of Milne, *Algebraic Groups* (2017), Corollary 14.9,
printed p.282 (PDF p.298). The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete official errata snapshot registered as
`milne-2017-algebraic-groups-errata-2026-11-02` was read; it does not change
Corollary 14.9. In the original proof, the parenthetical reference following
the first occurrence of “coconnected” reads 14.9; the criterion being used
is Theorem 14.5.

For any fields `k K : Type u` equipped with `Algebra k K`, and any actual
affine group scheme `G` of finite type over `Spec k`, the proposition asks
that `IsUnipotent G` imply `IsUnipotent` of its actual pullback to `Spec K`.
The base morphism is exactly
`Spec.map (CommRingCat.ofHom (algebraMap k K))`, and the pullback is the
published `GroupScheme.baseChange`. Finite type is expressed by
`LocallyOfFiniteType G.X.hom` together with `IsAffineHom G.X.hom`;
an affine morphism is quasi-compact. These conditions express the
algebraic-group scope of the source. Smoothness and connectedness are not
assumed.

Both unipotence predicates are the published ones: every nonzero
finite-dimensional matrix representation has a nonzero fixed vector,
with fixedness tested on every relative scheme. Thus the conclusion
quantifies over all representations over `K`, including representations
that do not descend to `k`. Preservation of fixed vectors for scalar
extensions of representations alone does not prove this proposition.
There is no perfectness, characteristic, algebraicity, separability or
cardinality restriction on either field or on the extension.

Milne proves preservation through the coconnected coordinate-coalgebra
criterion and proves reflection through scalar extension of fixed vectors.
Only preservation is stated here. This module supplies a proposition
target, not a proof or an assumed replacement for that structural argument.
Its intended use is to base change smooth connected normal unipotent
closed subgroups before applying a geometric radical-triviality hypothesis.
