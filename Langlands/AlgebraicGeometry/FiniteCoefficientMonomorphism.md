# Finite coefficient descent of monicity

The theorem `Langlands.AlgebraicGeometry.FiniteCoefficient.monomorphism`
proves the unchanged published
`Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u}`
uniformly in every universe. For every commutative `R`-algebra `A`, the
specified map `f : X ⟶ Y` over `Spec R` has finite type source and relatively
quasi-separated target. If its base change to `A` is monic, then for each
finite subset `s` of `A` there is a finitely generated `R`-subalgebra `T`
containing `s` over which the specified map is already monic.

The kernel pair is formed in the category of schemes over the coefficient
base. The forgetful functor preserves its pullback, so the actual structure
morphism of the kernel pair is quasi-compact. Here quasi-compactness of `f`
follows from quasi-compactness of its source over the base and
quasi-separatedness of its target over the base.

The pullback functor preserves the kernel pair. Monicity over the supplied
algebra therefore gives equality of the two base-changed projections. The
published theorem
`AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`
descends the equality of their underlying scheme maps, with the prescribed
finite coefficients included. Its domain is the quasi-compact kernel pair,
and its locally finite type target is `X`. The second
pullback projection gives equality of the maps over the base. Finally,
equality of the kernel-pair projections implies left cancellation and hence
monicity at the finite stage. This argument is implemented in the helper
`exists_fg_mono`; the entry theorem installs its explicit monicity premise
as an instance and applies the helper.

The proof is an internal consequence of the published equality descent
theorem and the pullback and monomorphism APIs. It introduces no extra
hypotheses on the rings or schemes.
