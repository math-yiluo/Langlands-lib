# Actual normalized parabolic support images

This internal construction specializes the published smooth support filtration
to normalized parabolic induction and takes its actual images in normalized
parabolic Jacquet coinvariants. Its ingredients are the existing function
model, the existing quotient map, and elementary submodule image arguments.
It introduces no new representation-theoretic assumption or external result.

## Images in normalized Jacquet modules

For a block shape `B` over a commutative ring `F`, a complex representation
`ρ` of `GL_n(F)`, a positive character `δ` of its actual Levi, and a
`B.parabolic F`-stable subrepresentation `S`, `B.normalizedJacquetImage δ ρ S`
is the submodule image of `S` under `B.jacquetMk ρ`. Thus its elements are
exactly the classes of vectors belonging to `S`, as recorded by
`mem_normalizedJacquetImage`.

The ambient representation is the existing `B.normalizedJacquetOf δ ρ`.
The normalized action of a Levi element `m` on the class of `v` is
`δ(m)^(-1/2)` times the class of `ρ(m)v`, with the positive square root
embedded into the complex numbers. Parabolic stability puts `ρ(m)v` in `S`,
and scalar closure puts its inverse-half multiple in `S`; linearity of the
quotient map proves invariance of the image. This argument does not require
the quotient map to intertwine the untwisted Levi action.

The image construction is monotone in `S`. It takes the zero subrepresentation
to zero by `Submodule.map_bot`, and the full subrepresentation to the full
Jacquet module by the existing surjectivity of `jacquetMk`. No exactness
theorem is used.

## Normalized inducing data and naturality

`B.inducingFunctor χ` sends a smooth representation of the actual Levi to
its existing inducing representation of the parabolic: inflate along the
Levi projection and twist by the inflated character `χ`. It sends an
intertwiner to `B.inducingMap χ`; the underlying linear map is unchanged.
Identity and composition laws follow directly.

For any prime, actual `PadicField`, compatible `TopologicalData T`, rank
and two block shapes `B,C`, `parabolicInductionSupportFiltration T B C s`
precomposes `s.rawSmoothSupportFiltration` with
`B.inducingFunctor (T.leviHalfCharacter B)`. This gives a filtration of the
actual normalized induction functor restricted to `P_C`, with the positive
half of the explicit block modulus on the inducing covariance. There is no
compact-support condition in this function space.

Here `s : OrderedDoubleCosets P_B P_C m` is supplied. At a step `k`, the
support condition is containment of the projected nonzero support in
`s.initialOrbits k`, the union of the first `k` specified orbits. The
representative convention remains the imported one: the orbit attached
to `w` consists of points `P_B w⁻¹ q` for `q ∈ P_C`. The construction
retains this ordering and uses the already proved support stability,
naturality, monotonicity, and endpoint identities.

`parabolicJacquetImageSubfunctor` maps any such natural parabolic-stable
subfunctor into the Jacquet quotient using
`C.normalizedJacquetImage (T.leviModulus C)`. An induced morphism sends the
class of a function to the class of its image. Naturality of the original
support subfunctor therefore supplies a representative in the required
target subspace, proving naturality of these quotient images.

## Filtration and scope

`parabolicJacquetSupportFiltration T B C s` applies this image construction
at every step. Its ambient functor is exactly the published
`jacquetInductionFunctor T B C`. Monotonicity follows from image monotonicity;
the zero and full endpoints follow from the corresponding support endpoints
and the image laws above. The field universe `uF` and input representation
universe `uV` remain independent, with output carrier universe `max uF uV`.
These elementary constructions do not require positive rank.

The module constructs natural subfunctors and their finite filtration for
the supplied ordered orbit data. It does not construct that ordering,
identify successive quotients with `geometricPieceFunctor`, prove a
compact-to-smooth induction comparison, or prove the geometric lemma.
In particular, passing to images alone asserts no exactness or graded
isomorphism. Those remain additional obligations for the main theorem.
