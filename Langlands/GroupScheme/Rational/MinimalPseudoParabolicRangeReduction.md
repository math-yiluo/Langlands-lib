# All-test range reductions for minimal pseudo-parabolic conjugacy

Author: Worker 274.

This supporting module proves the range and minimality steps used in the
rational conjugacy argument. It does not prove
`MinimalPseudoParabolicConjugacyStatement` or assume that statement.

The first two lemmas concern any group scheme over any base scheme in universe
`u`. If two subgroup functors lie in the image of a monic group-scheme
homomorphism, then every point fppf-locally in their ordered product lies in
that same image. The proof retains the cover in the published
`FppfLocallyInProduct` witness. Flatness, surjectivity and local finite
presentation make the cover an effective epimorphism. Both factors lift into
the represented subgroup, so their product does also; the published
`mem_range_of_comp_mem_range` descends this lift to the original test scheme.
No quasi-compactness assumption on this cover is needed. Applying this
pointwise proves `IsFppfProduct.range_le`.

`IsClosedSubgroup.sourceIsoOfRangeEq` works over the same arbitrary base. For
two closed subgroup homomorphisms with equal images on every relative scheme
test, this definition applies `isoOfIsRepresentedBy` to construct an actual
isomorphism of their sources. Its `sourceIsoOfRangeEq_hom_comp` theorem shows
that the isomorphism commutes with the inclusions. Together with the identity
rational point, `SubgroupConjugate.of_range_eq` then supplies precisely the
published `SubgroupConjugate` predicate.
`of_conjugate_range_eq` composes this with the conjugacy by the supplied
rational point. In particular, the conclusion includes the scheme structures
and an actual source isomorphism.

The remaining two lemmas work over an arbitrary field in universe `u`.
`IsMinimalPseudoParabolicSubgroup.subgroupConjugate_of_range_le` uses the
published minimality predicate to turn containment of a pseudo-parabolic
subgroup in a minimal one into equality of all-test images, then applies the
previous construction. The last lemma applies this after a supplied rational
conjugation. Its pseudo-parabolic property and all-test containment are still
explicit hypotheses; this module does not discharge their geometric proofs.

These are internal consequences of the existing definitions and represented
subgroup/effective-epimorphism lemmas. Their intended application is the last
containment-to-equality step of Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Theorem C.2.5, printed p.595 (PDF p.621), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The implemented descent and Yoneda arguments make the source's subgroup
containment and equality precise for the published all-test predicates.
