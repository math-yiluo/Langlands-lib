# Augmentation-compatible degree-zero maps

This internal extension of `EquivariantGodementCohomology` proves compatibility
of its existing degree-zero identification with chain maps between two mapped
cokernel complexes. The two source abelian categories have independent object
and morphism universes; the common target abelian category has two more.

For monic coaugmentations `η : 𝟭 A ⟶ T` and `η' : 𝟭 A' ⟶ T'`, let `Φ` and
`Ψ` be additive functors to the common target, preserving finite limits.
Given a chain map `t` and a map `a : Φ.obj M ⟶ Ψ.obj N`, the single compatibility
hypothesis says that the image of the first actual augmentation, followed by
`t.f 0`, equals `a` followed by the image of the second actual augmentation.

`cyclesIso_map` proves the corresponding square on cycles by composing with
the monic inclusion of target cycles and using the augmentation hypothesis.
`homologyZeroIso_inv_map` then composes with the natural homology projection.
`homologyZeroIso_map` gives the same square for the forward existing
degree-zero isomorphisms by cancellation with their inverses.

The construction uses the actual existing kernel-based `cyclesIso` and
`homologyZeroIso`; it introduces no new identification or resolution.
It is an internal consequence of those definitions and chain-map naturality,
with no assertion about higher exactness or right-derived functors.
