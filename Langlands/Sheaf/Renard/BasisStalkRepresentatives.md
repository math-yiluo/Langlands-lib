# Renard II.2.1: representatives of the actual basis stalks

This proof targets the published, closed proposition
`Langlands.Sheaf.Renard.BasisStalkRepresentativesStatement.{u,v}`.
The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed p.34 /
PDF p.40: the explicit representative description of the stalk and its
common-smaller-neighborhood equivalence relation. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original PDF pp.39–40 were read. The separately registered 2010-edition
*Corrections et compléments*, PDF pp.2–3, were checked supplementarily;
those pages do not change this stalk description.

The implemented proof uses the existing `BasisNeighborhood B x`,
`stalkDiagram F x`, `rawStalk F x` and `rawGerm F U x hx`. In particular,
the stalk remains the published abelian-group colimit, and the germ remains
its coprojection applied to the lifted original section.

Mathlib's `Algebra/Category/Grp/FilteredColimits.lean`, at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`, supplies
`AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`.
For carriers in universe `max u v` its filtered index size is initially
`max u v`. The private instance in this proof applies
`CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink` to obtain
preservation at the actual neighborhood category's object and morphism
size `u`. The imported construction already supplies filteredness of
`BasisNeighborhood B x` and existence of the colimit of `stalkDiagram F x`.
Thus preservation is proved for the actual diagram, with no preservation
hypothesis in any public theorem.

`rawStalk_representative` applies
`CategoryTheory.Limits.Concrete.colimit_exists_rep` from Mathlib's
`CategoryTheory/Limits/ConcreteCategory/Basic.lean` to this diagram and
its actual colimit element. This result uses the colimit of underlying
types obtained by preservation of the additive colimit. It returns a
basis neighborhood and a lifted section. Destructing the `ULift`
returns an original section in `Sections F U`; the coprojection equality
is then precisely the required `rawGerm` equality.

`rawGerm_eq_iff` applies
`CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists` to the two
lifted original sections. For a filtered diagram, this states that their
coprojection images agree exactly when they have equal images at a
common successor. These concrete results use Mathlib's underlying-type
colimit representative theorem and
`Types.FilteredColimit.isColimit_eq_iff`, respectively. A successor
here is an actual smaller basis neighborhood containing `x`. The two
arrows yield its two inclusions into the original neighborhoods.
`stalkDiagram_map_apply` identifies the images with lifts of the
original restrictions. Applying `ULift.down` gives equality in the
original section group. Conversely, a witness of equality of original
restrictions gives the two neighborhood arrows, and applying `ULift.up`
gives the equality required by the same colimit criterion.

`stalk_representative` and `germ_eq_iff` specialize these results to
exactly `F.obj`; the normalized stalk and germ unfold to those raw
constructions. The source-normalized formulation is the one in
Renard's presheaf category. The raw formulation is a derived extension
to arbitrary underlying restriction functors: the proof never uses
the empty-open normalization. Finally, `basisStalkRepresentatives`
universally quantifies the supplied space, topology and basis and
assembles all four components into the exact published aggregate.

The space and original-section universes `u` and `v` stay independent.
Only the stalk's existing carriers and the intermediate lifted sections
use `max u v`; every returned representative and every final restriction
equality uses original sections in universe `v`. Basis refinements are
existential, and no intersection is required to be a basis member.
There are no added sheaf, separation, countability, compactness,
nonemptiness, nontriviality or preservation assumptions. Empty spaces
give vacuous pointwise assertions; an empty basis open cannot contain
the supplied point. Zero section groups are allowed throughout.

The target statement and its imports are unchanged. Germ separation,
canonical maps, sheafification descent and adjunction, support, and the
basis/all-open comparison remain separate units.

Worker 595 authored this proof and its explanation.
