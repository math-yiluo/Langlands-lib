# Actual relative Weyl transporters and source cosets

This is an internal specialization of `RelativeWeylTransporterCosets` to the
actual normalizer/full-centralizer quotient. It implements the source-coset
comparison needed for Renard, *Représentations des groupes réductifs p-adiques*,
version of 9 July 2026, V.4.3–V.4.4 (printed p.119, PDF p.125) and VI.5.4
(printed pp.173–174, PDF pp.179–180). The generic construction and this
dependent-predicate interface are derived formalization tools.

The actual subgroup family `L` is assumed injectively indexed by finite
subsets of Coxeter labels. Each subgroup must contain the full centralizer of
`T`. The actual Levi Weyl identification must identify the image of
`WeylIn T (L J)` with the standard Coxeter subgroup at `J`.
`actualOvergroupFamily` places this family in the published Weyl conjugation
action. The source standard subgroup fixes its own Levi: by the identification,
each element comes from the source Levi Weyl quotient, whose action is inner
on that Levi.

`actualTransporterSelection` retains a normalizer lift `n`, an equality between
the literal conjugate of the source subgroup and the target subgroup, and an
arbitrary additional condition `Q J n h`. The condition can therefore express
the existence of an equivalence of representations along that precise
conjugation map. No independence of representation transport from the chosen
lift is assumed or asserted.

`actualMinimalTransporterCosetEmbedding` sends a minimal selected pair `(J,w)`
to the coset of `w` modulo the actual source Levi Weyl image. The selected
witness makes it a transporter in the actual action. Rewriting the source
subgroup using the Levi Weyl identification then reduces injectivity to the
generic embedding. `card_actualMinimalTransporterPairs_le` gives its natural
cardinality bound when the actual Weyl group is finite. The module makes no
representation-theoretic finite-length or Hom-dimension assertion.
