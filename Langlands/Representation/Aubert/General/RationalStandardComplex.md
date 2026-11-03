# The normalized Aubert complex on the actual rational-point family

This internal consumer construction specializes the published `StandardComplex`
to the actual group `RationalPoint k G.X` and the exact standard point families
`RationalPointFamily.parabolic`, `levi` and `unipotent`. All declarations are in
`Langlands.Aubert.General.RationalPointFamily`. The motivation is Aubert (1995),
printed pp.2186–2187, and the official erratum (1996), printed p.4687 display
(*), and p.4690 Remark (1), display (**). It supplies constructions and intrinsic
adapters, not the corrected exactness or consequence theorems.

`standardParabolic_monotone` and `standardUnipotent_antitone` evaluate the named
`GroupScheme.StandardParabolicOrderStatement` at the identity test object,
using the actual `rootSet` inclusion equivalence. Similarly,
`standardParabolic_univ` and `standardUnipotent_univ` evaluate
`StandardParabolicEndpointsStatement`, after `rootSet_univ`. Thus order and
endpoints are not free subgroup-family fields. Their named structural
statements, connected reductivity, maximal splitness and genericity of the
cocharacter remain explicit inputs.

`rootAssociation i ν hN hZ I J n` requires the actual ambient point `n` to
normalize the image of the torus points and its class to carry exactly
`rootSet i ν I` onto `rootSet i ν J` under `weylCharacterAction`. That action is
the published character action transported through the exact scheme/point
normalizer and full-centralizer comparisons `hN` and `hZ`. The support-category
predicate separately checks that the same point conjugates the two actual Levi
subgroups. This definition does not assert cuspidal-support uniqueness,
existence, or invariance.

The complex aliases explicitly install `pointTopology` on this exact ambient
group. They require its local compactness and nonarchimedean group structure,
closedness of the actual radicals, and their compact-limit property.
`isSemidirectDecomposition_of_standardCocharacterStatement` supplies the
decompositions, rather than a chosen abstract model.
`standardUnipotent_isUnimodular` derives the normalization prerequisite from
the compact-limit input. No finite-length premise is present. The separate
linear order on the actual simple-root subtype chooses exterior coordinates;
consumers can obtain its finite enumeration from `simpleRelativeRootFintype`
under `HasRelativeRootSystem` and splitness. No canonical order is asserted.

`rationalDegreeObject`, `rationalDifferential`, `rationalBoundary`,
`rationalTerminalProjection`, `rationalSharpObject`, `rationalSharpFunctor`,
`rationalInitialMap`, `rationalInitialEquiv` and
`rationalInitialDifferential` are the corresponding published constructions
with these literal families and derived laws substituted. In particular their
maps are the same canonical quotient-induced transitions, with the same
exterior orientation, square-zero law, naturality, incoming-image quotient and
surjective terminal projection already proved for `StandardComplex`.
`rationalInitialEquiv` additionally uses the two derived full-root endpoints.
The degree counts removed roots, and the retained cokernel at `|S|-|I|` has
coordinates indexed by standard subsets of cardinality `|I|`. No final zero
or terminal vanishing is added, including when the simple-root set is empty.

This module proves no general reductive structural statement, topological
closedness or compact-limit assertion. These remain named intermediate
obligations, subject to the parent's external-structural-input ledger.
Support theory, two-sided Bruhat filtration, graded transition comparison,
corrected Theorem 3.6, terminal Jacquet comparisons and finite-length,
irreducibility and involution results remain separate representation-theoretic
targets. Proposition 3.2 remains unresolved. No classification-independence
claim follows from these intrinsic substitutions.
