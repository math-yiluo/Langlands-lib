# Actual geometric terms for arbitrary surviving-class lifts

Worker 167. This internal construction derives representative comparisons from
the actual full-Levi geometric-term isomorphism, the published composition and
inner-conjugation comparisons, and the actual normalizer/full-centralizer
quotient. It introduces no additional literature assertion.

The generic constructions use closed Levi and radical families in an arbitrary
locally compact nonarchimedean group, with independent index, group and carrier
universes. The term comparisons use the saturated carrier universe `max uG uV`
required by the actual induction functor. Source and target intersection
semidirect decompositions remain explicit inputs.

`geometricTermInnerIso` identifies a self term represented by an actual element
`m` of the source Levi with the original smooth representation `A`. The
full-Levi comparison first identifies the term with inverse-conjugation
pullback. The published `conjugationFunctorInnerIso` then intertwines it with
`A` by the invertible action of `m`.

`geometricTermRightInnerIso` assumes inverse conjugation by `n` identifies the
entire target and source Levis. The term represented by `n * m`, for any
source-Levi element `m`, is isomorphic to the pullback represented by `n`.
The composition membership comparison supplies full conjugacy for `n * m`.
After the full-Levi term comparison, the inverse of the published conjugation
composition isomorphism expresses the pullback as `c_n(c_m(A))`. Mapping the
inner-conjugation isomorphism through `c_n` gives the asserted result.

`geometricTermSameWeylClassIso` assumes a subgroup `S` whose full centralizer
lies in the source Levi, and two normalizer elements `n` and `r` with the same
class in `N(S)/Z(S)`. Full-Levi conjugacy is required for the reference lift `r`.
The quotient equality puts `r⁻¹ * n` in the full centralizer and hence in the
source Levi. The preceding right-inner comparison, with this element as `m`,
identifies the actual term at `n` with the conjugation pullback at `r`.
The construction produces an actual representation isomorphism; it does not
identify the conjugation maps on subgroup elements.

`conjugationFunctorInversePullbackIso` compares inverse-conjugation pullback
at `n⁻¹` with pullback along the inverse of `conjugationEquiv n hConj`.
The identity linear map intertwines the two actions because
`n⁻¹⁻¹ * x * n⁻¹ = n * x * n⁻¹`. This helper involves no induction and
retains an arbitrary carrier universe `uV`.
`geometricTermSameInverseWeylClassIso` combines it with the same-class term
comparison for a lift of the inverse class of a reference normalizer element.

The rational specializations use the canonical evaluation topology
`pointTopology`, actual simple-root labels and actual standard subgroup
families. Their independent field and carrier universes are `u` and `v`;
the original representation carrier universe is `max (u + 1) v`.

`normalizerLift_mem_levi_of_mk_eq_one` uses only the point-centralizer comparison:
a lift of the identity Weyl class lies in the full point centralizer, which
agrees with the scheme-centralizer points and is contained in every standard
Levi. No reductivity, root-comparison, finite-root or nonempty-root premise is
needed for this elementary membership statement.

`pointGeometricTermIdentityClassIso` applies the generic inner comparison to
that Levi element. It identifies the actual normalized self term with the
original object for every lift of Weyl class `1`, rather than requiring the
literal element `1`. Closedness, local compactness, the nonarchimedean topology
and both actual intersection decompositions are retained.

`pointGeometricTermInverseLongestClassIso` retains the connected-reductive,
maximal split torus, generic-cocharacter and standard-cocharacter inputs,
point-normalizer and point-centralizer comparisons, finite roots and Weyl
group, actual Coxeter system, root-length and positive-simple-reflection
comparisons, minimality criterion and associated-subset laws. Fix any normalizer
lift `n` of `longestRep actual J`. Every normalizer lift `r` of its inverse class
gives an actual term from source `J` to target `associatedSubset actual J`
isomorphic to pullback along
`(associatedLeviConjugationEquiv ... J n hn).symm`.
The standard-Levi conjugacy theorem supplies full conjugacy for `n`, the inverse
membership theorem supplies it for `n⁻¹`, and the quotient inverse law gives
equality of the classes of `r` and `n⁻¹`. The generic
`geometricTermSameInverseWeylClassIso` then gives exactly the displayed inverse
associated-Levi pullback, using the identity linear comparison in its generic
inverse-pullback helper.

These are objectwise isomorphisms of individual actual geometric terms. They
require no maximality, non-self-association, cuspidality, irreducibility or
finite-length preservation premise. They do not construct a normalized
filtration, identify an induced Jacquet module with a surviving grade, or prove
`RationalRankOneSelfAssociationStatement`.
