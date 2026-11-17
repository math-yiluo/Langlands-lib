# Geometry of a supplied group affinization

`Langlands.GroupScheme.AffinizationGeometryStatement.{u}` isolates the
geometric step in the canonical affine quotient construction. For an arbitrary
field `k : Type u`, a smooth connected actual group scheme `G`, an actual group
scheme `Q`, and an actual homomorphism `q : G ⟶ Q` satisfying the unchanged
`IsAffinization q`, it asserts that `Q` is smooth and connected, and that `q`
is flat, surjective and quasi-compact. The affine target is part of
`IsAffinization`, which also requires an isomorphism on global functions.
Smoothness and affineness imply that `Q` is of finite type over `k`.

The source is SGA 3, Exposé VI_B, Theorem 12.2(i), printed page 430 / PDF page
100, Gille–Polo recomposed edition of 13 October 2024, with the smooth connected
specialization of its algebraic source. The general image assertion used there
is Corollary 11.18.1, printed page 427 / PDF page 97. The target here is any
supplied affinization: `IsAffinization.targetIso` and
`IsAffinization.comp_targetIso` identify it and its projection with the canonical
scheme affinization. Smoothness of the target follows by faithfully flat descent
from a smooth group; connectedness follows from surjectivity. The complete
Tome I errata dated 13 October 2024 do not alter these results.

This is a derived supporting statement for `AntiAffineQuotientExistenceStatement`.
It asserts neither the existence of the group structure on the affinization nor
anti-affineness or smoothness of its full kernel. No affine, quasi-compact,
finite-type, perfect-field, or algebraically-closed-field condition is added on
`G`: the published `quasiCompact_of_smooth_connected` and `fieldSeparated`
results supply the needed algebraic hypotheses. This file defines a proposition;
it does not supply its proof.

Source identifier: `sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
