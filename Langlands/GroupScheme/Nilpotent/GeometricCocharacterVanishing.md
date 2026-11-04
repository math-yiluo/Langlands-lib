# Geometric cocharacter vanishing for nilpotent groups

This internal deduction applies the commutative geometric cocharacter vanishing
theorem to the full scheme-theoretic center of a nilpotent group.

`NilpotentGeometricCocharacterVanishingStatement` quantifies over any field
`k : Type u` and a smooth connected affine geometrically nilpotent group scheme
`G` over `k`. It assumes that every homomorphism from every `k`-torus into `G`
has bottom subgroup-functor range. It concludes that every actual cocharacter
of the pullback of `G` to `AlgebraicClosure k` is zero.

The implemented proof represents the full center by a closed subgroup using
the fixed subgroup of self-conjugation. Its inclusion is central and monic,
so its source is an actual commutative group scheme. The center is affine
and locally of finite type because its inclusion is closed and the ambient
group is affine and smooth. Monic postcomposition reflects bottom range,
so the center inherits the original no-torus hypothesis. No smoothness or
connectedness assumption is imposed on the center.

The all-test center and its representing inclusion commute with field base
change. Geometric nilpotence of the ambient smooth connected affine group
also survives field base change. Centrality of torus homomorphisms into a
nilpotent group therefore factors each geometric cocharacter through the
geometric center. The commutative geometric vanishing theorem kills this
factor, and the factorization equality kills the original cocharacter.

`IsNilpotentGroupScheme.gm_hom_eq_zero_over_algebraicClosure` implements this
argument, and `nilpotentGeometricCocharacterVanishing` proves the named
proposition. The deduction uses `Nilpotent.TorusDescent`, the full-center
representability and base-change proofs, and `Torus.GeometricCocharacterVanishing`.
It does not yet deduce unipotence from geometric cocharacter vanishing and
does not prove the general `NoTorusUnipotentStatement`.
