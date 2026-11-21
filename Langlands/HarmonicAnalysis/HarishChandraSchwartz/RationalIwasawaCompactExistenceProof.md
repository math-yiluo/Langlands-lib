# Compact open Iwasawa subgroups on rational points

`Langlands.HarishChandraSchwartz.rationalIwasawaCompactExistence` proves the published
`RationalIwasawaCompactExistenceStatement` in the same namespace. For a connected reductive
group scheme over a nonarchimedean local field, it supplies a maximal split torus, a generic
cocharacter and a compact open subgroup \(K\) in the canonical rational-point topology.
Every rational point is a product \(p k\) with \(p\) in the empty-index standard parabolic
and \(k\) in \(K\).

The statement is the existence assertion used in the compact picture of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*, §I.1,
printed p. 240 (registered source `waldspurger-2003-plancherel`). The proof below obtains
the required minimal-parabolic product by using depth-zero root groups at an apartment
point and the relative Tits system.

## Valuation data and the point stabilizer

`nonempty_valuationBuildingData` uses `exists_maximalSplitTorus` and
`specialTorusExistence` to choose a maximal split torus over the ground field and a
special torus that becomes maximal split over the maximal unramified extension.
`connectedReductiveFieldExtensionStatement` and `unramifiedQuasiSplit_of_henselianDiscrete`
with `henselianDiscreteQuasiSplit` give connected reductivity and quasi-splitness after
base change. `quasiSplitIntegerApartmentExistence` produces the valuation datum, its
centralizer comparison, and V6 over the extension. The opposite-pair hypothesis for
`unramifiedValuationDescent` follows from `rootRankOneFactorization` and
`RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs`. Descent supplies
the data and V6 on the ground-field torus needed to form `ValuationBuildingData`.

For a point \(x\) of that apartment, use
`ValuationBuildingData.compactStabilizer (B.apartmentMap x)` as the subgroup.
`KPApartmentData.rootFixer_singleton`, `KPApartmentData.rootFixer_le_sharpFixer`
and `ValuationBuildingData.sharpFixer_le_compactStabilizer` put every depth-zero
root group in the stabilizer. So does the actual centralizer norm kernel by
`ValuationBuildingData.map_mem_compactStabilizer`.
`ValuationBuildingData.isTopologyCompatible` supplies the filtration topology.
`RelativeRoot.openRootCentralizerGeneration`, with the openness of the root
filtrations and the centralizer norm kernel, shows that these subgroups
generate an open subgroup. The stabilizer is therefore open.

`IntegerValuationBuildingData.ofLocalApartmentEquiv` and `ofLocal_filtration`
transport algebraic boundedness of the depth-zero root groups to integer
valuation data. `IntegerValuation.characterValuationKernel_normalized` identifies
the centralizer kernel with the bounded norm-kernel image. Then
`IntegerValuationBuildingData.isAlgebraicallyBounded_oneStabilizer` gives boundedness
of the integer one-stabilizer, and `ofLocal_oneStabilizer` identifies it with
the chosen stabilizer. Its closure is compact by algebraic boundedness.
The stabilizer is closed because it is an open subgroup, so it is compact.

## A point admitting compact representatives of the simple reflections

`IsSplitTorus.exists_genericCocharacter` chooses the generic cocharacter. At an arbitrary
apartment point, `IsRootDatumValuation.exists_ne_top` uses V0 to find a finite-valued
element in each simple relative root group. The V1 field `eq_top_iff` then shows that
each chosen element is nonidentity. These are the roles of V0 and V1 in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Definition 6.1.2, printed p. 199
(PDF p. 230, registered source `kaletha-prasad-2023-bruhat-tits-new-approach`).
The simple roots form a finite, linearly independent set by `relativeRootSystem`.
`rootEvaluation_surjective` gives a torus-space vector whose evaluation on each
simple root is the negative of its chosen value. Translating by the image of this
vector in `TranslationSpace` sets all those values to zero by
`KPApartmentData.val_mk_vadd` and `RootFunctionFamily.vadd_apply`.

`rootRankOneFactorization` gives a normalizing representative of each simple
reflection from its chosen root element. Each representative fixes the translated
point by `RootReflectionProof.hasRootReflections` and belongs to the common norm
kernel by `ValuationBuildingData.reflectionElement_mem_rationalCommonNormKernel`.
The equivariance of `apartmentMap` then puts each representative in \(K\).

## Product with the minimal parabolic

Let \(X = P_0(F)K\). It contains the identity and is stable under left multiplication
by \(P_0(F)\) and right multiplication by \(K\). The kernel identity from
`relativeTitsSystem` shows that two normalizing representatives of the same
Weyl element differ on the left by an element of \(P_0(F)\). Thus for each simple
reflection the left-stability check can use the chosen representative \(j\) in \(K\).

`hasSimpleRootParabolicFactorization_of_statements`, applied with `relativeRootSystem`,
`standardParabolicEndpoints`, `genericCentralizer` and
`RelativeRoot.dynamicRootOrderedProduct`, writes a parabolic element as \(b'u\).
Here \(u\) belongs to the simple-root group and \(jb'j^{-1}\) is still parabolic.
`IsRelativeReflection.weylAction_apply_self` and `conj_mem_rootGroupPoints` put
\(e=juj^{-1}\) in the negative-root group. If \(e\) belongs to its depth-zero
filtration, then it belongs to \(K\). Otherwise `rootRankOneFactorization` writes
\(p_1 e p_2=m\) with both factors in the positive-root group and \(m\) representing
the same simple reflection. This last identification uses `IsRelativeReflection.of_neg`
and `HasRelativeRootSystem.eq_of_isRelativeReflection`.

The right factor \(p_2\) has nonnegative value. The proof applies axiom V5 to
\(p_2^{-1} e^{-1} p_1^{-1}\) and uses `RootReflectionProof.apply_inv`. The sum
of the values of \(p_2\) and \(e\) is zero, and the value of \(e\) is strictly
negative. Hence \(p_2\) belongs to \(K\). The left factor \(p_1\) belongs to
\(P_0(F)\) by `RelativeRoot.subgroup_le_standardParabolic_empty`. Write
\(m=zj\) with \(z\) parabolic by the same kernel identity. Then
\(e=(p_1^{-1}z)(jp_2^{-1})\) belongs to \(X\).

It follows that \(j b'u k=(jb'j^{-1})e(jk)\) belongs to \(X\) for every \(k\)
in \(K\). `Langlands.Group.IsTitsSystem.mem_of_stable` concludes \(X=G(F)\).
The resulting factorization, together with openness and compactness, supplies
all the witnesses of `RationalIwasawaCompactExistenceStatement`.
