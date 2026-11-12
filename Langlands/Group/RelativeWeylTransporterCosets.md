# Minimal transporters and source Weyl cosets

This internal algebraic construction supplies the injective comparison needed
in the numerical bounds of Renard, *Représentations des groupes réductifs
p-adiques*, version of 9 July 2026, V.4.3–V.4.4 (printed pp.119, PDF p.125)
and VI.5.4 (printed pp.173–174, PDF pp.179–180). The generic group-action
formulation and its proof are derived here; they are not a separately numbered
assertion in that source.

Fix a Coxeter system on a group `W`, a family `x` indexed injectively by finite
subsets of its simple labels, and a source index `I`. Suppose the standard
subgroup `W_I` fixes `x I`. An arbitrary predicate `P J w` can select
transporters. `minimalTransporterPairs` consists of pairs `(J,w)` such that
`w` is minimal in `W_J w W_I`, transports `x I` to `x J`, and satisfies `P`.
`transporterSourceCosets` is the image, in the quotient by `W_I`, of all
selected transporters to any member of the family.

`minimalTransporterCosetEmbedding` sends `(J,w)` to the coset `w W_I`.
Equality of two such cosets gives `w⁻¹v ∈ W_I`. Since this subgroup fixes
the source, the two elements act identically on it. Injectivity of the family
then identifies the target indices. The two Weyl elements lie in the same
double coset for that common target and the fixed source, so the published
uniqueness of minimal Coxeter double-coset representatives identifies them.
No transitivity or conjugacy-completeness assumption is used.

`card_minimalTransporterPairs_le` derives the natural-cardinality inequality
from this embedding when `W` is finite. Finiteness of the indexing type is
unnecessary. The construction alone proves neither representation-theoretic
bound of VI.5.4; those also require the geometric filtration, Jacquet detection,
and the comparison of its surviving grades with actual Levi transporters.
