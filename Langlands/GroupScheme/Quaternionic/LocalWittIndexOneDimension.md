# The dimension bound for local quaternionic forms of Witt index one

This internal module, an input to the enumeration of actual rank-one Tits
indices over nonarchimedean local fields (`LocalRankOneTitsIndexStatement`),
proves that a nondegenerate
trace-valued antihermitian form of Witt index one has at most three variables
over a four-dimensional division algebra whose involution has a
three-dimensional symmetric subspace. The ground field is any
nonarchimedean local field. Every field and residue characteristic is
included, and the ground field, algebra and coordinate index have independent
universes.

## The actual scalar quadratic form

`sesqFormBilinear` regards the original division-algebra-valued pairing as
a bilinear map over the central ground field. Rank-nullity for the map
`a ↦ a - σ(a)` shows that the alternating subspace has dimension one under
the dimensions four and three. This repeats the elementary argument of the
published `QuaternionConjugation` module with independent universes for
the field and division algebra.

For any such alternating line, `alternatingCoordinate` chooses a
ground-field linear functional on the division algebra whose kernel meets
that line only at zero. Its construction chooses a nonzero generator and a
dual functional taking that generator to one. Every member of the line is
a scalar multiple of the generator, which proves the required injectivity.
No value away from the alternating line is prescribed.

`traceValuedQuadraticForm` composes that functional with the diagonal of
`sesqFormBilinear`. This is an actual `QuadraticForm K (n → D)`. For a
trace-valued antihermitian matrix, every self-pairing belongs to the
alternating line. Consequently the scalar quadratic form vanishes exactly
where the original self-pairing vanishes. The construction never divides by
two.

## Implemented dimension proof

`eq_zero_of_ortho_of_wittIndex_one` proves anisotropy on the common
orthogonal complement of vectors `e,f` with `h(e,e)=0` and `h(e,f)=1`.
If a nonzero vector `y` there had zero self-pairing, the vectors `e,y`
would be independent: applying `h(-,f)` to a relation first kills the
coefficient of `e`. The antihermitian identity makes their pairing vanish
in both orders. They would therefore span a totally isotropic plane,
contradicting Witt index one.

`card_le_three_of_wittIndex_one` chooses `e` and its hyperbolic partner from
the published form lemmas. Define the division-algebra-linear map
`x ↦ (h(x,e), h(x,f))`, and regard its kernel `W` also as a ground-field
space. The scalar quadratic form restricted to `W` is anisotropic by the
preceding argument. The published
`Langlands.localQuadraticAnisotropicDimensionBound` gives
`dim_K W ≤ 4` without a characteristic or polar-nondegeneracy restriction.
The tower law `dim_K W = 4 * dim_D W` implies `dim_D W ≤ 1`.
The map's range has dimension at most two. Rank-nullity then gives
`card n ≤ 2 + 1 = 3`.

## Provenance and scope

All definitions and arguments here are internal constructions from published
Library results and elementary linear algebra. The only local arithmetic
input is the unconditional all-characteristic quadratic dimension bound
in `LinearAlgebra/LocalQuadraticAnisotropicDimensionBound`. The geometric
pairing and Witt-index lemmas come from the quaternionic form modules.
This result does not use local rank-one group classification or
Kneser--Tits, and it does not itself assert the full enumeration of actual
Tits indices.
