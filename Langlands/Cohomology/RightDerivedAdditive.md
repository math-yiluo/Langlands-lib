# Additivity of right derived functors

The instance `Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive F n`
states that `F.rightDerived n` is additive when `F : C ⥤ D` is an additive functor
between abelian categories and `C` has injective resolutions. The object and
morphism universes of the two categories are independent.

The sum of the chosen lifts `InjectiveResolution.desc f` and
`InjectiveResolution.desc g` lifts `f + g`. The proof uses
`Functor.rightDerived_map_eq` to compute the derived map through that sum,
then uses additivity of the induced homology maps.

This is the unchanged generic instance from Worker 958’s published
`AlgebraicGeometry/Modules/CechResolution/Acyclic` module. It retains its full
declaration name and is shared by the Čech-resolution and divisible-system
modules without requiring algebraic-geometry imports.
