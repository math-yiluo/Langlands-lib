# Determinant twists of GL Whittaker coefficient models

Worker 31 specializes the constructions from
`Langlands.Representation.Whittaker.AlgebraicTwist` to the actual GL Whittaker
models. The original `Langlands.twist` and its open-kernel smoothness theorem
remain imports from Worker 4's published branch. The general linear group
and determinant are imported from the geometry branch.

For GL of rank `n + 1`, compose an actual unit-valued character of the field
units with the actual determinant. The determinant of an upper-unipotent
matrix is one: Mathlib's upper-triangular determinant formula reduces it to
the product of its diagonal entries. The general construction therefore
specializes to `determinantTwistFunctionalEquiv` and
`determinantTwistModelEquiv` for the standard Whittaker character. The first
equivalence retains the functional; the second multiplies its actual
coefficient functions by `χ(det g)` and intertwines the scalar-twisted source
model with the coefficient model of the twisted representation. Continuity
of the determinant pulls an open kernel in the field units back to an open
kernel in GL, supplying the smoothness specialization. Every positive rank,
including rank one, is covered. The field carrier's universe is independent
of the representation-space universe. The algebraic GL construction in fact
uses only a commutative ring; complex coefficients are used for its Whittaker
functionals.

The source convention for the Whittaker coefficient image is Jacquet,
Piatetski-Shapiro and Shalika, *Rankin--Selberg Convolutions* (1983),
section 0.3, printed page 377, and section 2.1, printed pages 385-386.
Registered original `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Those source pages were read directly. This pair's multiplier and image
equivalence are derived algebraic consequences of the coefficient formula,
not additional theorems quoted from the original. The imported twist pair
documents its determinant-twist convention and source.

Both imports are published Library modules: `AlgebraicTwist` (which imports
`Langlands.Representation.Twist.SmoothProof`) and `GeneralLinear` (which imports
the actual group `Langlands.GeneralLinear`, its `determinant` and
`determinantContinuous` from `Langlands.Group.GL.Basic`, and the upper-unipotent
subgroup from `Langlands.Group.GL.UpperUnipotent`). This pair adds no new
character, group or twist; it only proves the determinant hypothesis and
instantiates the general constructions.

No irreducibility, multiplicity one, genericity existence, or local-factor
transformation law is assumed or proved. In particular, the pair does not
claim that the twisted model is the unique Whittaker model of the twisted
representation.
