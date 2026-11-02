# Renard II.2.1: representatives and equality of basis germs

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed p.34 / PDF p.40,
the explicit equivalence-class description of the stalk immediately before
the sheafification functor. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original PDF pp.39–40 were read directly. The separately registered
2010-edition *Corrections et compléments*, PDF pp.2–3, do not correct this
stalk passage; that supplementary check is limited to those pages.

`StalkRepresentativeStatement F x` states the representative-existence part
of the source description: every element of the existing `stalk F x` equals
the existing `germ F U x hx s` of an original section
`s : Sections F.obj U` on an actual chosen basis neighborhood.
`GermEqualityStatement F x` states the source equivalence relation: the
germs of sections on two basis neighborhoods are equal if and only if there
exists an actual basis open `W` containing `x`, contained in both original
opens, on which their original restrictions agree. The two inclusion
witnesses are arguments to precisely `restriction F.obj`. The sections
being compared therefore lie in the same original group
`Sections F.obj W`.

These two assertions concern the source-normalized category `Presheaf B`,
whose underlying functor is exactly `F.obj`. The raw assertions
`RawStalkRepresentativeStatement` and `RawGermEqualityStatement` give the
same colimit assertions for every `RawPresheaf B`, using `rawStalk`,
`rawGerm`, `Sections F` and `restriction F` directly. This raw extension
does not use the source's empty-open normalization. It is a derived
generalization of the source description for the underlying restriction
functor.

`BasisStalkRepresentativesStatement` is the closed, aggregate proposition
containing all four assertions, universally quantified over the space,
its supplied topology, its chosen basis, each presheaf and each point.
The individual assertions further quantify over stalk elements,
neighborhoods, membership proofs and original sections as appropriate.
The space universe `u` and section-group universe `v` are independent;
the stalks retain the published carrier universe `max u v`.
All section groups, restrictions, stalk carriers and germ maps come from
`Langlands.Sheaf.Renard.BasisStalk` and its `BasisPresheaf` dependency.

Only the chosen basis property and the presheaf functor structure are
present. The assertions require no sheaf or separation condition,
intersection closure, compactness, countability, global nonemptiness,
nontrivial groups or external colimit-preservation hypothesis. The common
refinement is existential; the intersection need not be a chosen basis
open. Empty spaces are included, with the pointwise assertions vacuous.
An empty basis open cannot supply a neighborhood membership witness.

This module defines propositions. It supplies no proof of representative
existence or germ equality and constructs no explicit additive equivalence
with a quotient presentation. The all-open comparison, etale spaces and
sheafification remain separate obligations. The aggregate is intended as
the exact target of a later proof unit.

Worker 1215 authored the proposition definitions and documentation.
Worker 6 supplied the source audit and the specification of this focused
statement family.
