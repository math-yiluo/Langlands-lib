# Reduction of multiplicative-type centralizer openness to the split case

This is an internal reduction from the Library's field-level definition
`IsMultiplicativeType`, the all-test subgroup functors, and fpqc descent of
open immersions. It supplies no proof of the split input.

`DiagonalizableCentralizerOpenProperty` asks that a represented centralizer
inside a represented normalizer of a monic embedding of `D(M)` be an open
subgroup. It ranges over every field and every finitely generated abelian
character group `M`, including groups with torsion. The ambient group scheme
is arbitrary. In particular it assumes neither smoothness nor affineness.
The centralizer representative is specified as the preimage under the
normalizer inclusion, so its points are tested on every scheme.

`multiplicativeTypeCentralizerOpen_of_diagonalizable` proves that this input
implies the unchanged `MultiplicativeTypeCentralizerOpenStatement` in the same
universe. The splitting field and the group `M` come directly from
`IsMultiplicativeType`. The supplied subgroup embedding is transported through
its splitting isomorphism. Source isomorphisms preserve its range, and the
normalizer, centralizer, preimage and their representatives commute with
base change. The equation `f ≫ n = c` identifies `f` as a representative of
the preimage centralizer, by `IsRepresentedBy.comap_of_comp`.
The split input therefore proves openness of the base change of `f`.

The two descent helpers prove openness of `f` along an arbitrary fpqc base
change, and along any field extension, respectively. The underlying
base-changed map is a pullback along the target projection. That projection
is fpqc, so fpqc descent of open immersions applies. A field extension is
fpqc without any algebraicity, finiteness or separability requirement.

The target's finite-type hypotheses on the ambient group are carried through
unchanged but are not needed by this reduction; the closed-subgroup hypothesis
supplies the monicity used by the split input.
