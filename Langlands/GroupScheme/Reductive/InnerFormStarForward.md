# Inner forms have equivalent star actions

Internal development of the forward implication of
`InnerFormStarActionStatement`. The proof follows the geometric comparison in
Conrad, *Reductive group schemes* (2014), Lemma 7.1.1, pp.238–239, and Proposition
7.2.2, p.252, using the star action described on p.256.

The comparison lemmas treat any field extension and two supplied Galois pinning
data. A torus-compatible group isomorphism induces, under each field
automorphism, a discrepancy on the target group and target torus. The inclusion
square is checked using the canonical descent comparisons. Naturality of
character transport then identifies the full root action of this discrepancy
with the difference of the two ordinary Galois actions. If the discrepancy is
fppf-locally inner, its full root action is Weyl by
`SplitPinning.mem_weylGroup_of_locallyInner`. A comparison preserving bases thus
intertwines the two based projections, which are the star actions.

`exists_basedEquiv_of_innerEquivalent_pullIso` first aligns an arbitrary comparison
with both chosen tori and bases by rational conjugation. Inner equivalence is
preserved by composition and canonical pullback, so this adjustment preserves
innerness of every Galois discrepancy. The comparison lemma then applies to every
field automorphism.

Finally, `of_localIso` takes a local isomorphism over any separable field extension
with all-test inner discrepancy. It embeds that extension into the separable
closure and refines the local family along this embedding. The published
local-family/base-change-isomorphism equivalence recovers an actual comparison
over the separable closure. Evaluating inner discrepancy at the identity and
each Galois cover endomorphism makes every pullback inner-equivalent to this
comparison, so the previous lemma supplies the claimed based star equivalence.
In particular the result applies to every finite Galois inner-form presentation
in the target statement, without any extra hypothesis on the groups or centre.

`AbsoluteInnerComparisonStatement` defines the complete quantified proposition
proved by `of_localIso`, for all universes, fields, separable extensions,
affine groups of locally finite type, supplied adjoint quotients, and absolute
Galois pinning data. The theorem `absoluteInnerComparison` proves this definition
by applying `of_localIso` with those parameters.
