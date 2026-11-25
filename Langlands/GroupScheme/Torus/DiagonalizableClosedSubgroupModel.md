# Compatible character presentations of closed diagonalizable subgroups over fields

Derived interface for the fibre-kernel step of the
relative multiplicative-type kernel-factorization proof.

Let `k` be any field, `M` a finitely generated abelian group, and
`i : H → D_k(M)` a closed subgroup. `ClosedSubgroupModel i` consists of
a finitely generated abelian group `N`, a surjection `p : M → N`,
and an isomorphism `e : H ≅ D_k(N)` such that the actual inclusion
is `e.hom ≫ D_k(p)`. All character groups retain their torsion.

`nonempty_closedSubgroupModel` proves existence, and
`closedSubgroupModel` chooses the resulting data. The proof first uses the
published `Diagonalizable.closedSubgroupPresentation` to obtain `N` and
`e`. Published full faithfulness
`DiagonalizableCharacter.restrictMap_bijective` expresses `e.inv ≫ i`
as `D_k(p)`. Closedness and the published
`MultiplicativeTypeGaloisExactness.isClosedSubgroup_restrictMap_iff`
then imply that `p` is surjective. Cancelling the isomorphism gives
the asserted equality with `i`.

`kernelModel f` applies this interface to the actual scheme-theoretic
kernel inclusion of a homomorphism `f : D_k(M) → G` with separated
target `G`. Separatedness supplies closedness of that kernel inclusion.
No smoothness, connectedness or reducedness hypothesis is imposed.

This module is internal derived content: it packages compatibility between
existing Library theorems. It introduces no new literature transcription
and does not prove the relative kernel criterion.
