# Subrepresentation relations for a filtered union of compact subgroups

Author: Worker 269.

`Langlands.Jacquet.coinvariantSubrepresentationRelations` proves exactly
`Langlands.Jacquet.CoinvariantSubrepresentationRelationsStatement`, with the
published hypotheses and universes.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (9 July
2026), III.2.9, Corollary, printed p.80 / PDF p.86, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The internal lemma `relations_top_eq_ker` identifies relations for the top
subgroup with the ordinary representation coinvariant kernel by comparing their
generators. The internal lemma `compactOpenFiniteContainment` chooses a compact
open subgroup using the published Van Dantzig theorem. The union hypothesis
places each member of a finite set in a compact subgroup; filtering combines
these with the chosen compact open subgroup. Their common compact supergroup
is open, since it contains an open subgroup.

The main proof applies the published
`Langlands.coinvariants_map_injective_of_smooth` to the inclusion of the
subrepresentation, using that finite-containment lemma. A vector of the
subrepresentation whose ambient coinvariant class vanishes therefore already
has zero coinvariant class in the subrepresentation. The reverse inclusion
follows by mapping a zero class along the inclusion. Extensionality of
submodules yields the stated equality.
