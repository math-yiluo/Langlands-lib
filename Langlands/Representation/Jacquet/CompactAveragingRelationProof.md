# Haar averaging detects compact-subgroup coinvariant relations

Author: Worker 269.

`Langlands.Jacquet.compactAveragingRelation` proves exactly
`Langlands.Jacquet.CompactAveragingRelationStatement`, retaining both universes
and every published hypothesis. The existential compact subgroup works for
every Haar measure on that subgroup, as required by the statement.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (9 July
2026), III.2.9, Proposition, printed p.79 / PDF p.85, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The internal compact-group comparison first regards the published finite
orbit-mean projector as an endomorphism of the representation. Translation
invariance of orbit means and invariance of their outputs show that this
endomorphism intertwines the action. Naturality of `Hecke.fixedProjection`
therefore makes the two projectors commute. Each projector fixes the image
of the other, since both images consist of invariant vectors, so they are equal.
The published kernel theorem for the finite orbit-mean projector then
identifies the Haar projector's kernel with the usual relation submodule.
This comparison uses no topology on the representation space.

For the forward implication, finite compact-open containment and the published
`Langlands.coinvariants_mem_ker_iff_compact` place a relation vector in the
relation submodule of one compact open subgroup. Apply the compact-group
comparison to the representation restricted to this subgroup. It works for
any Haar measure there. Conversely, choose the canonical Haar measure on the
given compact subgroup. The comparison puts a vector killed by its projector
in the restricted relation submodule; the published restriction lemma embeds
this submodule into the ambient relation submodule.
