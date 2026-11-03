# The ambient torus in an actual standard Levi representative

This internal construction specializes the published represented-subgroup
factorization and maximal-split-torus transport to the existing choice-free
`standardLevi`. It is a prerequisite for comparing actual split components with
selected-root annihilators. It does not assert reductivity of the standard Levi
or realize the whole real annihilator by a split component.

The base field and universe are arbitrary. Let `i : T.toGrp ⟶ G` be a map from
a commutative group scheme, with `G` affine, and let `ν` and `J` specify the
standard Levi. No genericity, root finiteness, or subset premise is needed for
the containment and lift.

`range_le_standardLevi` combines `range_le_torusCentralizer` with
`torusCentralizer_le_standardLevi`, so its containment is on all test schemes.
For every actual representative `j : L ⟶ G`,
`standardLeviTorusFactor` is the published `factorHom` applied to this
containment. `standardLeviTorusFactor_comp` proves its composite with `j` is
the original map `i`. If `j` is closed and `i` is maximal split, the factor is
maximal split in `L`, by
`IsMaximalSplitTorus.isMaximalSplitTorus_factorHom`.
`IsMaximalSplitTorus.exists_standardLevi_lift` packages the actual map,
maximality, and composite identity.

`isCentral_standardLeviTorusFactor_of_le` assumes the standard Levi centralizes
one ambient cocharacter. Its proof sends an arbitrary point of `L` through
`j`, uses the all-test dynamic-centralizer condition to obtain commutation,
and cancels the representing monomorphism. Thus the cocharacter lifted through
the torus factor is central in `L`. The standard-cocharacter specialization
uses the defining intersection of `standardLevi`.

`isCentral_standardLeviTorusFactor_of_annihilates` retains the explicit premises
of the published `standardLevi_eq_cocharacterAnnihilatorCentralizer`: finitely
many simple roots and existence of a standard cocharacter for `J`. That equality
supplies the centralizer containment for every integral cocharacter annihilating
`J`, and the preceding cancellation proof gives its centrality in `L`.

These results are derived from the Library modules `StandardParabolic`,
`StandardLeviAnnihilator`, `LeviFactorization`, and `MaximalSplitTorusSubgroup`;
they introduce no additional literature assertion. The stronger unconditional
standard-Levi reductivity, real-image, and rank statements remain separate
proof obligations.
