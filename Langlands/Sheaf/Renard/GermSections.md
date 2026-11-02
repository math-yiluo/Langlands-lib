# Renard II.2.1: locally represented dependent germ families

Worker 633 implemented this construction. Worker 6 supplied the original-source
audit and the suggested additive-subgroup and refinement route.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, equation (II.2.1.2) and the
restriction, group and morphism constructions, printed pp.34–35 / PDF pp.40–41.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original pages were read in full and PDF p.40 was visually checked. The
supplementary registered 2010-edition *Corrections et compléments*,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3 were read. Its cover-index and later adjunction corrections do not
change this section carrier.

`GermFamily F U` is the dependent function type `(x : U) → rawStalk F x.val`.
Giving such a function is the fiber-respecting presentation of a section of
the disjoint union of stalks. No topology on that disjoint union is used.
`LocallyRepresented` requires a contained basis neighborhood at every point
and one original section whose germs agree with the family at **all** points
of that neighborhood. Representability of just the value at the chosen
point would be a weaker predicate and is not used.

`RepresentedOnCover` states the original cover formula, comparing on the
intersection of each representing basis open with the domain. Its supplied
cover index has independent universe `w`, and the representing opens may
extend outside the domain. `locallyRepresented_of_cover` refines that
intersection at the chosen point and restricts the original section; the
published `rawGerm_restriction` proves the germ formula. Conversely,
`LocallyRepresented.cover` chooses the local witnesses, indexed by the points
of `U`, and obtains a contained cover. `locallyRepresented_iff_cover` records
the equivalence. This existential cover has fixed index universe `u`; no
cardinality bound on the basis or on independently supplied cover indices is
assumed.

`germSectionSubgroup` cuts out precisely these families in the dependent
function group. The zero family is locally represented by zero on any
sufficiently small basis neighborhood. For addition the proof refines the
intersection of the two representing neighborhoods, restricts both original
sections and adds them. Negation uses the negative original section.
`GermSections` is this subgroup's actual subtype with its inherited
pointwise abelian group, and the three evaluation formulas expose zero,
addition and negation.

`germRestriction` is restriction of dependent functions to any smaller
actual open. Its membership proof refines the intersection of the smaller
open with a representing neighborhood and restricts the original
representative. Its evaluated formula and its identity and composition
laws are definitional. Sections on the empty actual open are subsingleton
because dependent functions there have empty domain.

`germSectionsMap` applies the published additive `rawStalkMap` at every point.
The germ naturality theorem proves local representation by the image of
the original local representative. Additivity follows pointwise. The
restriction law is definitional, and identity and composition follow by
evaluating the corresponding stalk-map laws. The explicit representative
formula identifies the image with the germ of `φ.app (op V) t`.

The space and original-section universes `u` and `v` remain independent;
the fibers and section groups live in `max u v`. Accepting an arbitrary
`RawPresheaf`, including one not normalized at empty, and retaining the
joint universe are internal extensions of the source construction. The
source-normalized specialization is obtained by the existing inclusion.
No sheaf or separation assumption, intersection-closed basis, local
compactness, countability, global nonemptiness or nonzero group hypothesis
is used. Empty spaces, empty covers and bases without an empty member are
included. Direct gluing and categorical sheaf packaging are supplied
separately; quotient representatives, the sheafification unit/adjunction
and the basis/all-open equivalence remain outside this module.
