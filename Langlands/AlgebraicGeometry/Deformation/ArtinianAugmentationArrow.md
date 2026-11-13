# The augmentation arrow of an Artinian test

For a commutative ring `k`, a field `K` with a `k`-algebra structure, and an
augmented Artinian test `A`, `augmentationArrow A` is the arrow from `A` to
the residue test whose algebra map is the augmentation of `A`. Its construction
uses `ArtinianTest.homMk` and makes no coefficient-field or section choice.

This module contains the unchanged definition formerly in
`Picard/ArtinianChartVersality`. It retains the full declaration name
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartVersality.augmentationArrow`
so existing callers keep their interface. The lower module permits reuse by
`ArtinianPrincipalKernelSquare` without importing Picard lifting theory.
