# Étale permutation atlases and their Weil-presentation target

`HasEtalePermutationAtlas D` is a predicate on an actual group scheme over
an arbitrary scheme `S`. Its data consist of a small jointly surjective
étale cover, a finite coordinate type for each member, and actual
group-scheme isomorphisms from the pullbacks of `D` to the corresponding
split tori. The coordinate types may be empty and may have different
cardinalities on different members.

`EtalePermutationAtlas.restrictChart` normalizes restriction of a chart
along `q : V ⟶ U` to a direct pullback along `r : V ⟶ S`, using an
explicit equality `q ≫ f = r`. It first uses the inverse of the
published `Descent.pullbackComparison`, then the pulled-back chart, then
the canonical split-torus base-change isomorphism.

`AgreeBy` says that two such normalized charts agree by a supplied
equivalence `σ : J ≃ I`: target coordinate `j` of the second chart
equals coordinate `σ j` of the first chart. This equality is required on
every test scheme over `V` and every point of the actual pulled-back
group scheme.

`LocallyPermutes` requires this agreement on an open neighbourhood of
every point of the actual fibre-product overlap. The common direct
pullback is along the first projection composed with the base map; the
pullback equation identifies the second composite with it. The
equivalence may depend on the open neighbourhood. In particular, the
predicate does not require a single permutation on a disconnected
overlap. No compatibility is imposed on an empty overlap.

`PermutationAtlasWeilPresentationStatement` asserts, in every universe,
that over `Spec R` this predicate implies the existence of a commutative
`R`-algebra `E`, finite and projective as an `R`-module and étale as an
algebra, with an actual group-scheme isomorphism
`D ≅ WeilGm.groupScheme (CommRingCat.of R) E`. The zero algebra is allowed.
Affineness of `D` is not a hypothesis.

This is an internal general descent interface extracted from the
simple-root permutation route to the adjoint-torus Weil presentation.
It is formulated using the published cover, split-torus, pullback
comparison, and Weil-restriction constructions. It does not prove
effective permutation descent or construct an atlas for a supplied
Borel and maximal torus. Those are separate proof obligations; no
additional hypothesis is added to the unchanged relative-Borel target.
