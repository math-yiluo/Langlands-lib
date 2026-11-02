# Renard II.2.1: sheaf germ separation and corrected target compatibility

This proof establishes exactly the published closed proposition
`Langlands.Sheaf.Renard.RenardSheafGermSeparationStatement.{u,v,w}`
through `renardSheafGermSeparation`. It supplies all six raw and normalized
component families, without any additional hypothesis on the aggregate.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed pp.35–37 /
one-based PDF pp.41–43. The zero-germ lemma and displays
(II.2.1.3)–(II.2.1.5) are on printed p.36 / PDF p.42. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Those three original pages were read directly. The supplementary registered
2010-edition *Corrections et compléments*, source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were checked in the preceding statement/source audit. Those
pages correct other cover and adjunction formulas; they are not the source
of the target-sheaf correction implemented here.

The proof imports the independently published `BasisStalkRepresentatives`
module. Its `rawGerm_eq_iff` applies to the existing actual stalk colimit
and gives equality of original restrictions on a common smaller basis
neighborhood. The present module does not reconstruct that colimit or its
representative relation. All sections, restrictions, germs and induced
stalk maps remain the published `BasisPresheaf`, `BasisSheaf` and
`BasisStalk` constructions.

`rawSheafZeroGermSeparation` assumes the literal `SheafCondition F` and
starts with an original section `s` on a basis open `U`. At each point of
`U`, its zero germ equals the germ of the zero section on `U`. Applying
`rawGerm_eq_iff` gives a smaller actual basis neighborhood on which the
restriction of `s` equals the restriction of zero, hence is zero by
additivity. The proof collects all such basis opens into a set cover
`C`: membership consists of an inclusion into `U` together with vanishing
of the original restriction. This set cover covers `U` by the preceding
pointwise argument. Its members carry the zero sections, whose
compatibility on every smaller basis open follows because restriction
maps preserve zero. Both `s` and zero are amalgamations of this family.
The uniqueness clause of `SheafCondition F` identifies them.

This is the source lemma's neighborhood-cover argument, using the set
cover of all vanishing restrictions instead of choosing one neighborhood
for each point. If `U` is empty, the pointwise covering assertion remains
valid and the same sheaf uniqueness proof still applies. No nonempty
point, index, open or space is chosen. Thus the proof uses the literal
sheaf condition also in the empty case; it does not discard that case
because the all-germs premise is vacuous.

`rawSheafGermEquality` applies zero-germ separation to `s - t`.
The existing germ map is additive, so equal germs of `s` and `t` make
every germ of their difference zero. The group identity `sub_eq_zero`
then gives `s = t`. `sheafZeroGermSeparation` and `sheafGermEquality`
specialize these two raw results to the actual underlying functor
`G.obj.obj` and its sheaf witness `G.property`. The existing normalized
`germ G.obj` is precisely the raw germ of that functor.

The printed inference of (II.2.1.3) from equality of original source
germs is false when the source is an arbitrary presheaf. The source
lemma has a sheaf hypothesis, which is unavailable for that source.
The independently published
[source-error audit](../../../notes/renard/basis-sheafification-source.md)
gives a normalized two-point counterexample and explains the repair.
Also, an arbitrary chosen basis need not contain the intersection of
two of its members. The present proof establishes the needed image
compatibility (II.2.1.4) on every actual smaller basis open.

Specifically, `rawTargetGermCompatibility` fixes two family members
`U i`, `U j`, an actual basis open `W`, and inclusions of `W` into both.
To compare the original target restrictions of the image sections, it
uses `rawSheafGermEquality G` on `W`, with the given target sheaf
condition. At each point of `W`, `rawGerm_restriction` identifies the germ
of each restricted target section with the germ of its unrestricted
image. `rawStalkMap_germ` identifies this with the actual induced
`rawStalkMap ψ x` applied to the corresponding original source germ.
Applying that map to the assumed source-germ equality identifies the
two target germs. Target separation gives equality of the restricted
image sections, exactly the literal `Compatible G` predicate.

`targetGermCompatibility` implements the same comparison directly in
the normalized categories. It uses `sheafGermEquality G`,
`germ_restriction`, `stalkMap_germ` and the actual `stalkMap ψ x`.
Its image components are the supplied morphism's original
`ψ.hom.app` maps. In both versions the source has no sheaf or separation
hypothesis, and the family has no covering hypothesis. Only the target
is required to be a sheaf. Equality is tested on `W`; neither source nor
target is evaluated on an intersection that may be outside the basis.

Finally, `renardSheafGermSeparation` universally quantifies the original
space, supplied topology and chosen basis, then assembles the six
component theorems in the published order. The space universe `u`,
original section-group universe `v`, and family-index universe `w`
remain independent. The original section groups stay in universe `v`;
only the already constructed stalks use `max u v`. No smallness,
intersection-closure, separation, countability, local compactness or
nonemptiness hypothesis is added. Empty families give vacuous literal
compatibility, and empty opens are covered by the uniqueness argument.

The raw separation formulation, subtraction consequence, cover-free
compatibility and closed aggregate are the derived packaging already
specified in the target. The target Lean/Markdown pair and every imported
pair are unchanged. Canonical units, actual descent maps, universal
factorization, the Hom equivalence, adjunction, support and the
basis/all-open equivalence remain separate units.

Worker 595 authored the Lean proofs and this implementation explanation.
Worker 6 supplied the original-source audit, corrected target-sheaf
argument and focused specification used here.
