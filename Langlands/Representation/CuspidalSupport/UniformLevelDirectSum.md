# Direct-sum tools for uniform compact-open detection

This internal module develops the direct-sum argument used in the reverse
direction of Renard VI.10.7, Variant. Its centre-admissibility statement
concerns actual smooth complex representations of any topological group.
It assumes every summand is centre admissible and that, at each compact
open subgroup, all but finitely many summands have zero fixed space.
It concludes that their actual algebraic direct sum is centre admissible.

The implemented proof chooses centre generators for the finitely many
active summands, includes them in the direct sum, and indexes their union
by a finite dependent sum. Every fixed vector has zero coordinates outside
these summands. Its componentwise centre expansions therefore combine into
one finite expansion. Naturality along the summand inclusions identifies
each included centre translate with the corresponding centre translate
in the direct sum. A finite-type equivalence relabels the generators by
`Fin n`, as required by the published `IsCenterAdmissible` predicate.

The module also proves that an actual direct sum of infinitely many nonzero
smooth representations is not finitely generated over the group algebra.
It applies the published finite-coordinate-support theorem to the identity
map of the sum. A coordinate projection outside that finite support would
be zero, contradicting its retraction onto a nonzero summand.

Finally, `Langlands.exists_antitone_compactOpen_basis` supplies a decreasing
sequence of compact open subgroups cofinal in the identity neighbourhoods
of a first-countable weakly locally compact nonarchimedean group. It applies
Mathlib's countably-generated-filter subbasis theorem to the published
compact-open subgroup basis. This topological auxiliary uses no
representation-theoretic assumptions.

Provenance is derived: this is an algebraic supporting step for David
Renard, *Représentations des groupes réductifs p-adiques*, version dated
9 July 2026, VI.10.7, Proposition and Variant (printed pp.216–217 /
PDF pp.222–223), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source does not state this direct-sum lemma separately. This module
does not prove the complex finite-type characterization or the family
characterization.
