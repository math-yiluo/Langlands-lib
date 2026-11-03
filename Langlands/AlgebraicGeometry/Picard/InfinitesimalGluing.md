# Actual Picard comparisons for affine infinitesimal squares

This internal construction defines the canonical restriction comparison
needed to state an infinitesimal gluing theorem for the actual relative
Picard groupoid. It uses only the existing actual line-bundle pullback
pseudofunctor, its composition isomorphisms, the relative total-space
functor, and the affine base attached to an algebra. It asserts no
effectivity or equivalence theorem.

For a commuting square of actual schemes
`Y0 -> Y1 -> Y` and `Y0 -> Y2 -> Y`, `SquareGluingData` is the comma
category of the two actual Picard pullback functors to `Y0`.
An object is a line bundle on `Y1`, a line bundle on `Y2`, and an actual
isomorphism between their ordinary pullbacks to `Y0`. A morphism is a
pair of actual bundle isomorphisms satisfying the overlap square.
Every such morphism is invertible, and the groupoid instance retains
the inherited category operations.

`squarePullbackIso` compares the two successive ordinary pullbacks
using `PicardGroupoid.pullbackComp` on each side and transport along
the equality of the composite scheme maps.
`squareGluingComparison` sends a bundle on `Y` to its ordinary
restrictions with exactly that overlap identification. Its action on
arrows is ordinary pullback on each component; compatibility is
naturality of the comparison isomorphism.

`relativeSquareComparison` applies this construction to the actual
base-changed total schemes of a commuting square in `Over S`.
No alternative model of the family or quotient by bundle isomorphisms
is introduced.

For commutative algebras at universe `u`, `affineBaseMap` sends an algebra
homomorphism to its contravariant spectrum map as an actual arrow over
the spectrum of the coefficient ring. Its composition formula is the
ordinary contravariant composition formula for `Spec`.
`affineSquareComparison` specializes the preceding construction to
four algebras `R, A, B, C` and a ring pullback square
`R -> A -> C`, `R -> B -> C`. The algebra structures and all four
algebra homomorphisms are retained. The categorical ring-pullback
condition supplies the commuting-square equation; no assertion that
the resulting comparison is an equivalence is made here.

The coefficient ring need not be a field and the scheme morphism need
not be proper for these constructions. Surjectivity and nilpotence,
which are needed in the intended infinitesimal gluing application,
are also not needed merely to define this comparison.
