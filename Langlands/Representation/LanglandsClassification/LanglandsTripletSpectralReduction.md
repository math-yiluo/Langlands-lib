# Opposite regularity: the remaining spectral separation and exact assembly

Author: Worker 135. This internal reduction identifies the remaining
Langlands-specific exponent obligation. It proves conditional implications,
not the VII.4.1 Lemma unconditionally.

`LanglandsTripletOppositePieceSeparationStatement` retains every object and
hypothesis of the published opposite-regularity target. For every family of
representatives of the actual double cosets and every geometric-lemma
intersection datum below the identity in the Bruhat relation, it asserts that
the generalized split-component weights of the full geometric-lemma piece
of the twisted representation are disjoint from its inducing exponents.
The full pieces and their actions are the published `pieceFunctor`; no
abstract replacement spectrum is introduced. This is the separation used in
Renard VII.4.1, expressed in the full-piece convention of the published
`PQRegularityLemmaStatement`. It is unproved in this module.

`langlandsTripletOppositeKernel_of_pieceSeparation` proves that the represented
geometric lemma, the VII.3.3 regularity criterion and that separation imply
the kernel-comaximality clause. The geometric lemma supplies a finite
enumeration of actual double cosets, representatives and intersection data.
The proof reindexes those data by the enumeration's inverse to produce the
input required by the regularity criterion. Twisting preserves irreducibility,
so the inducing twist has finite group-algebra length. The finite-length
direction of the criterion then yields exactly `IsPQRegular`.

`langlandsTripletOppositeRegularity_of_pieceSeparation` combines this with the
previous identity-support and dimension reduction to give the exact published
target, conditionally on four propositions: opposite identity support, the
represented geometric lemma, the regularity criterion and the newly isolated
piece separation. All four remain explicit hypotheses; this module does not
prove them. The universes `u` and `v` remain independent, and no target file
or transitive import is changed.

The provenance is internal assembly of published interfaces. The separation
premise is motivated by Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VII.4.1, printed pp.241–242 /
PDF pp.247–248, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 135 read these pages. The source proves separation on the Jacquet
factor before inducing it; the full-piece formulation follows the convention
of the published VII.3.3 criterion and retains the comparison with that
factor as part of its unproved spectral obligation.
