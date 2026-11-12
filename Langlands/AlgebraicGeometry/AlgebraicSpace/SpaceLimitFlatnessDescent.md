# Flatness descends along cofiltered affine limits for algebraic spaces

Author: Worker 156.

`SpaceLimitFlatnessDescentStatement` is the flatness conjunct of the assigned
statement, proved by `spaceLimitFlatnessDescends`. It
imports unchanged chart-based flatness, chooses fixed affine locally finitely
presented chart schemes at the original stage, and uses flatness independence
of the chart square. Restriction of that square to any scheme base change
compares flatness of the space map with flatness of the actual base-changed
scheme map. Pullback symmetry identifies the slice-pullback convention with
the convention of the published scheme relative flatness descent theorem.

Restrict the original cofiltered affine diagram along `Over.forget i`, where
`i` is the original stage. This forgetful functor is initial, so the
restricted cone is still a limit cone. The map of its diagrams to the
original affine stage comes from the actual incoming arrows of `Over i`.
The scheme relative flatness descent theorem supplies an equivalence with an
incoming stage. The chart comparison at the cone and at each incoming stage
then gives exactly `SpaceLimitPropertyDescends (fun f => IsFlatMorphism f)`.

The argument is an internal consequence of the cited published scheme theorem
and the supporting chart constructions. It retains arbitrary cofiltered
categories and universes, and the existing hypotheses on the original spaces.
It adds no representability, smoothness, or noetherianity assumption. The
scheme-chart transport comes from `SpaceMorphismBaseChange`. The
geometrically connected fibre and pure fibre dimension conjunction remains
outside this supporting unit.
