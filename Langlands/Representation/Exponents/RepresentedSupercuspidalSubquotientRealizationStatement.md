# Realization of an admissible supercuspidal subquotient

Author: Worker 1781. The proposition
`Langlands.Aubert.General.RepresentedParabolic.RepresentedSupercuspidalSubquotientRealizationStatement`
states the Lemma of Renard VI.3.6 for arbitrary actual connected reductive
groups over a nonarchimedean local field. It is a prerequisite statement;
this contribution supplies no proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.3.6, Lemma and proof, printed
pp.147–148 / PDF pp.153–154. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passage was read directly.

For an admissible smooth complex representation `π` and an irreducible
supercuspidal smooth representation `τ` of `G(k)`, the source assumes that
`τ` is isomorphic to a subquotient of `π` and concludes that `τ` is both
a subrepresentation and a quotient of `π`. The Lean conclusion uses
`SmoothRep.IsSubrepresentation τ π` and `SmoothRep.IsQuotient τ π`.
These mean existence of an actual injective intertwiner `τ → π` and
an actual surjective intertwiner `π → τ`. The maps are not required
to exhibit `τ` as a direct summand. For irreducible `τ`, this is the
source's equivalent assertion that both Hom spaces are nonzero.

Admissibility is the published `SmoothRep.IsAdmissible` predicate:
smoothness and finite generation of fixed vectors for every open
subgroup. Over the complex numbers this is finite dimensionality.
Supercuspidality is written out as vanishing of the normalized actual
`jacquetFunctor` for every proper actual rational parabolic, with a
rational Levi subgroup, matching geometric unipotent radical and
the multiplication isomorphism. It is the same predicate as in
the represented VI.5.2–VI.5.4 targets.

The field universe `u` and common carrier universe `v` are independent.
The common carrier universe is the one used by the published actual
subquotient relation; the statement imposes no bound relating it to `u`.
The rational-point topology is the canonical published topology.
Local compactness and the nonarchimedean-group instance are explicit,
as in the represented VI.5 targets. No standard parabolic, finite-length,
central-character, semisimplicity, category-decomposition, admissibility
of `τ`, or structural-comparison premise is added. The source derives
the maps through the cuspidal category decomposition and a finite
dimensional commuting-operator argument; formal proof remains a
separate obligation.
