# Actual general-linear points and coordinate-smooth families

Let `n` be any finite type with decidable equality, `R` a commutative ring,
and `A` a bundled commutative `R`-algebra. Let `B` be a complete normed
commutative ring with a normed real-algebra structure, and fix a ring
homomorphism `c : A →+* B`. The coefficient ring `A` needs no topology;
continuity, injectivity, and surjectivity of `c` are not assumed.
Let `M` be any charted space with a real model with corners `I`.

`coefficientCoordinates` is a group homomorphism from the actual relative
scheme points `(groupScheme n R).affinePoints A` to `GL n B`.
It first applies the existing general-linear scheme-point equivalence,
then maps every matrix entry and inverse entry through `c`.
`coefficientCoordinates_entry` identifies each resulting entry with `c`
applied to evaluation of the corresponding regular entry section.

`coordinateSmooth_iff_contMDiff` proves that a family of actual points
`p : M → (groupScheme n R).affinePoints A` satisfies the all-regular-function
criterion `CoordinateSmooth A c I p` if and only if
`x ↦ coefficientCoordinates n R A c (p x)` is real `C∞` as a map into
the existing manifold on the units of `Matrix n n B`. The conclusion is
about the image family after `c`; a noninjective coefficient map may
deliberately weaken either equivalent condition. The finite type may be
empty.

The matrix algebra uses Mathlib's submultiplicative row-sum norm, selected
by `Matrix.Norms.Operator`, as in `Langlands.Global.ArchimedeanGL`.
Its units have the existing real manifold structure as an open subset of
that complete real normed algebra. Entrywise assembly uses a continuous
real-linear map from finite product coordinates into this matrix algebra;
the proof does not identify their norms.

In the forward implication, regular entry sections give smooth matrix
entries. Finite product assembly gives a smooth matrix-valued map, and the
open embedding of units into the matrix algebra gives smoothness into
the unit group. In the reverse implication, projection from the matrix
algebra and smooth inversion give smooth entries and inverse entries.
Every regular function in the general-linear coordinate algebra is
represented by a polynomial in these generators. Polynomial induction,
smooth addition and multiplication, and the existing scheme-point
evaluation identity prove every required test.

This is an internal derived comparison using the existing actual point
equivalence, regular sections, coordinate-algebra classification, and
Mathlib's unit-group manifold. No external algebraic-to-analytic theorem
is used. It constructs no manifold on the points of a general group scheme.
Specializing the coefficient algebra to infinite adeles and `c` to their
mixed real/complex coordinates is possible when the stated instances are
supplied; this module does not yet identify automorphic function spaces,
construct differential operators, or prove growth or reduction theorems.
