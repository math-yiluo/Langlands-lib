# Local reciprocity under compatible conjugation

This module is a derived consequence of the published local reciprocity,
closed-commutator quotient, and finite Artin transport APIs. It works with an
actual p-adic field `F`, a supplied topological datum `T`, and supplied
reciprocity candidates. It does not construct the candidates.

The first three lemmas prove uniqueness under
`LocalReciprocityCandidateRelation`, which contains geometric order
normalization and the profinite norm-residue relation. This is weaker than
`GeometricWeilReciprocityRelation`, because no residue normalization is used.
The implemented proof follows the published uniqueness proof: actual finite
abelian norm kernels compare membership in every open subgroup of the Galois
abelianization; integer degree quotients determine the common procyclic
generator when valuation is nonzero. Multiplication by a uniformizer extends
the comparison to valuation zero. Injectivity of the Weil-to-Galois
abelianization map then gives equality of the candidates.

For transport, let `b` be a ring automorphism of `F`, let `θ` be an automorphism
of its chosen algebraic closure satisfying the displayed algebra-map square,
and let `c` be a continuous multiplicative automorphism of the actual local
Weil group. The projection compatibility hypothesis says
`projection(c(y))(θ(x)) = θ(projection(y)(x))` for every Weil element and closure
element. `restriction_conjugation` proves the corresponding identity on every
actual finite abelian extension, using the conjugate extension and its Galois
equivalence from `FiniteArtinTransport`.

`unitsEquiv` is the actual units equivalence induced by `b`, with continuity
of `b` and its inverse supplied for `T`'s topology. Writing this equivalence
as `B`, and writing `C` for the published `abelianizationCongr c`,
`transportedCandidate` sends a supplied candidate `e` to `B⁻¹ ∘ e ∘ C`.
This is a continuous multiplicative equivalence of the same actual Weil
abelianization with the field units. Its inverse is `C⁻¹ ∘ e⁻¹ ∘ B`.

`transportedCandidate_finiteFamily` identifies the finite Artin family of this
candidate with the published pullback of `e`'s family through `b` and `θ`.
The proof chooses a Weil representative of `e⁻¹(B(a))`, applies the finite
restriction conjugation formula to its inverse-conjugate representative,
and descends through the actual quotient projections. Thus the published
finite Artin pullback theorem supplies all norm kernels, surjectivity and
restriction coherence. Density is preserved because each candidate inverse
is surjective and the comparison to the Galois abelianization is fixed.

`transportedCandidate_relation` additionally assumes that `b` preserves the
order homomorphism on units and that `c` preserves the actual integer degree.
These assumptions transport geometric order normalization, so the new
candidate satisfies the same local candidate relation. Applying the weaker
uniqueness theorem gives `reciprocity_conjugation`: for every actual Weil
element `y`, `e(projection(c(y))) = B(e(projection(y)))`.

All compatibility, continuity, order and degree hypotheses are explicit. This
unit does not discharge them for the finite Galois conjugation construction.
That specialization, the associated Weil extension cocycle and its arithmetic
fundamental-class identity remain obligations of the host task. No map into a
prescribed class extension or desired extension-class identity is assumed or
claimed here.
