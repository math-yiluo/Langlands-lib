# An actual universal Borel family from a universal parabolic family

Workers 633 and 285.

`RelativeLevi.BorelSchemeData G` bundles an actual parameter scheme over the
arbitrary base scheme `S`, a group scheme over that parameter, its inclusion
into the pullback of `G`, and proofs that the inclusion is relative Borel, that
every relative Borel subgroup on every test scheme has a unique classifying
morphism, and that the parameter scheme is smooth and proper over `S`.
Classification uses equality of subgroup functors on every test scheme, as in
the unchanged published `RelativeBorelSchemeStatement`.

`borelSchemeDataOfParabolic` constructs these data from a supplied universal
relative parabolic family `j` with smooth proper parameter scheme `M`. Its
other explicit premises are reductivity of `G` and the published proposition
`RelativeBorelLocusClopenStatement`. It does not construct a universal
parabolic family or assume that parabolic representability has been proved.
All constructions and assertions have an arbitrary universe parameter `u`.

This derived construction implements Conrad, *Reductive group schemes*
(2014), proof of Theorem 5.2.11(3), p.158, using the open and closed locus of
Theorem 5.2.11(1). Its parameter is literally the open subscheme
`borelParameter hcl hG j hj` of `M`, its group is the pullback of the supplied
parabolic source along the open inclusion, and its inclusion is the actual
`familyHom` of that inclusion, including the ambient pullback comparison.

The open inclusion has image in the Borel locus by the range formula for an
open subscheme. The family criterion proves that the restricted inclusion is
relative Borel. Given any relative Borel inclusion on a test scheme, the
supplied parabolic universality gives a unique parameter in `M`. Equality of
all-test subgroup functors transfers Borelness to that evaluated family; its
parameter image therefore lies in the Borel locus.
`existsUnique_evaluate_openParameter` lifts the parameter uniquely to the
open subscheme and preserves the required evaluation equality. The existing
geometry of `borelParameter` supplies smoothness and properness, with
closedness of the locus used for properness.

The output contains the actual scheme and universal family, with their proved
properties. Its hypotheses remain visible: the construction alone does not
prove the unconditional Borel-scheme target.
