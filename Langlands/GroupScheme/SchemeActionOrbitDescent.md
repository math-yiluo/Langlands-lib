# Descent of a subgroup-fixed orbit through an fppf quotient

This derived construction uses the published scheme action and orbit morphism,
the full scheme kernel in `RelativeRoot.IsFppfQuotient`, and the published
`FiniteIndexTransfer.exists_factor` and
`Dynamic.flagQuotient_hom_ext_of_local_lift` descent lemmas. It introduces no
geometric existence assumption and does not prove a fixed-point existence
theorem.

For a section fixed by a subgroup on every scheme test, its orbit morphism
is constant on right cosets: write the second point as the first times a
subgroup point, and apply the action multiplication and fixedness laws.
Two points with the same quotient image differ by a point of the scheme
kernel. The assumed equality of the kernel range and subgroup range then
gives precisely the coset condition.

For a quasi-compact represented fppf quotient, the existing fpqc descent
lemma supplies a morphism from the quotient to the target whose pullback is
the original orbit. `descendedOrbitMap` chooses this actual relative
morphism, and `quotient_comp_descendedOrbitMap` proves its restriction law.
The auxiliary `quasiCompact_quotient` proves quasi-compactness of any
group-scheme morphism over a field with affine source, using the published
field-separatedness theorem for its target and quasi-compactness of the
source's structure morphism.

Every such orbit factor is equivariant on all tests. Pull back a given
quotient point along the fpqc morphism; on the resulting cover it has a
lift to the original group. The orbit restriction law and action
multiplication law prove equivariance there, and the existing local-lift
extensionality lemma descends the equality. The argument applies over any
field and in any universe, including nonreduced test schemes and targets.

These lemmas are internal categorical consequences of the cited published
APIs. Their intended consumer is the proof of the unchanged
`SplitSolvablePseudoCompleteFixedPointStatement`; the elementary quotient
limit argument and the finite-series induction remain separate obligations.
