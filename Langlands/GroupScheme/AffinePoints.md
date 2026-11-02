# Coefficient points of a group scheme

For an actual group scheme `G` over `Spec R`, `affinePoints G A` is the group
of morphisms `Spec A → G` over `Spec R`. Its group law is the one already
constructed by the group-valued Yoneda functor. No affine, reductive, split,
smooth, or finite-type hypothesis is needed for evaluating this functor.

The existing unbundled `Lie.AffinePoints` and `Lie.affineMap` definitions and
their identity/composition lemmas are shared here from
[Lie/DualNumberKernel](Lie/DualNumberKernel.md), with their names and proofs
unchanged. Worker 339 authored that interface. `affinePointMap` reuses its
coefficient map with bundled `CommAlgCat` coefficients. The bundled
`affinePoints` abbreviation spells out the definitionally equal actual
morphism carrier using the original bundled algebra `A`. This preserves
its syntactic form for typeclass inference and rewriting: reconstructing
`A` from its underlying ring and algebra can hide the bundle from downstream
topology instances. No point carrier, group law or coefficient map is changed.

`affinePointFunctor` restricts that existing functor to affine test schemes.
`affinePointMap` extends coefficients along an algebra homomorphism by
precomposition with its spectrum map. The identity and composition laws
follow from functoriality. `affinePointsTarget` applies a group-scheme
homomorphism by postcomposition; its compatibility with coefficient
extension is associativity of scheme morphisms.

These are internal restrictions of the existing
`Langlands.GroupScheme.points` and `pointsMap`, not a new algebraic-group
structure. They supply the coefficient points used in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §2.2, printed
pp. 51–54, especially the point interpretation preceding Theorem 2.2.1.
The source is registered as
`getz-hahn-2024-automorphic-representations`.
This file constructs the groups and maps; the topology in that theorem
requires a separate construction.
