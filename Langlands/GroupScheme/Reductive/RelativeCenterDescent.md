# Descent of diagonalizable scheme-theoretic centres

This internal construction supplies the descent step of Conrad, *Reductive
group schemes* (2014), Theorem 3.3.4, pp. 98–99. It uses the Library's
all-test centre functor and effective closed-subgroup descent. It does not
assert that an arbitrary group has a diagonalizable centre: local closed
diagonalizable centre representatives are explicit inputs.

For any group scheme `G` over any scheme `S`, and any étale covering family
`𝒰` of `S`, `center_eq_coverDescent` identifies `center G` with the subgroup
defined by membership in its pullbacks on every test over each cover member.
One containment is naturality. For the other, two products whose equality
expresses commutation become equal after pulling the covering family back to
the test scheme. The resulting effective epimorphism family detects equality.
There are no affineness, smoothness, connectedness or finiteness assumptions.

`center_isClosedRepresentable_of_etaleCover` applies the published effective
closed-subgroup descent theorem to this equality. Matching follows because
the local functors are pullbacks of the actual centre functor, and the
published arbitrary-base-change theorem identifies them with the centres of
the pulled-back groups.

`relativeCenterModelOfEtaleCover` constructs a group scheme `Z` over the
original base and a closed inclusion into `G` representing the full
scheme-theoretic centre, assuming each local centre has a closed
diagonalizable representative. Its pullback to every cover member is
isomorphic to the supplied local representative by uniqueness of subgroup
representatives. Diagonalizability transports across these actual
group-scheme isomorphisms. Regarding the étale cover as an fppf cover then
witnesses `RelativeMultiplicativeType.IsMultiplicativeType Z`.

`relativeCenterModelOfEtaleCover_baseChange` records that the chosen
inclusion remains a full scheme-theoretic centre after every base change.
`exists_multiplicativeTypeCenter_of_etaleCover` packages the construction
and that property in the existential form needed by the relative-centre
target. The implementation uses the published centre base-change theorem;
it does not replace scheme-theoretic centres by geometric-point centres.

Provenance: this is a derived internal construction from the Library's
effective closed-cover descent, effective epimorphism detection and
all-test centre base-change results. Conrad's proof motivates the passage
from local root-kernel centres to a global centre; the present module
implements only that passage and its multiplicative-type conclusion.
