# Affine full-centre quotients over arbitrary bases

Worker 221.

`Langlands.GroupScheme.relativeAdjointQuotientExistence.{u}` proves the
unchanged Library proposition
`Langlands.GroupScheme.RelativeAdjointQuotientExistenceStatement.{u}`.
For every scheme `S` and reductive group scheme `G` over `S`, it constructs
a group scheme `A` over `S` and a homomorphism `q : G → A` such that `A → S`
is affine and `RelativeRoot.IsFppfQuotient (center G) q` holds.

The quotient predicate asserts that the underlying scheme map is flat,
surjective and locally of finite presentation, and that the range of its
actual kernel inclusion is `center G` on every relative scheme test.
The centre tests commutation after every further test morphism, so this
identification retains its full scheme-theoretic structure. The base may
be non-affine, non-quasi-compact, disconnected or non-Noetherian, and the
centre need not be smooth or reduced. The quotient and its map are
conclusions, with no supplied quotient, action or additional hypothesis.

The implemented proof applies the published reduction
`relativeAdjointQuotientExistence_of_center_and_centralMultiplicativeTypeQuotients`
to the two published unconditional theorems `reductiveRelativeCenter` and
`relativeCentralMultiplicativeTypeQuotient`, all in universe `u`.
The first theorem supplies a closed full-centre inclusion `z : Z → G`
with `Z` of relative multiplicative type. In the reduction, reductivity
supplies smoothness and relative affineness of `G` and connectedness of
its geometric fibres. The full-centre inclusion is central, so the second
theorem constructs an affine group quotient by `SubgroupFunctor.range z`.
The equality of that range with `center G` gives the required quotient
predicate. The centre theorem's further base-change clause is not needed
in this assembly.

This is an internal consequence of the stated Library theorems and the
published reduction. Its mathematical provenance is the centre theorem
and central multiplicative-type quotient construction in Brian Conrad,
*Reductive group schemes* (2014), Theorem 3.3.4 and the proof of Lemma 3.3.2,
printed/PDF pp.98–99, as recorded in the paired target and input modules
(registered source `conrad-2014-reductive-group-schemes`). The proof
establishes precisely affine full-centre quotient existence; reductivity
and triviality of the centre of the quotient are separate conclusions.
