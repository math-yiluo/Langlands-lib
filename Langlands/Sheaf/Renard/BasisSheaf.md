# Renard II.2.1: the literal basis sheaf condition

This unit implements condition (F) and the category `Sh(X)` in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, printed pp.33–34 / PDF pp.39–40, ending at the sentence defining `Sh(X)`.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original pages were read and visually checked. The separately registered
2010-edition errata PDF pp.2–3 contain later sheafification corrections, which
are outside this unit and do not alter its definitions.

The imported `BasisPresheaf` supplies an actual chosen basis `B` of the supplied
topology, its thin inclusion category, and normalized contravariant abelian-group
functors. The space universe `u`, group-carrier universe `v`, and arbitrary-family
index universe `w` remain independent. The basis need not contain empty or
pairwise intersections. There are no separation, local compactness, cardinality
or countability assumptions.

`FamilyCovers V U` means every family member is contained in `V` and every
point of `V` belongs to a member. `Compatible F U s` compares the two restricted
sections on **every basis open** contained in both selected members. It never
requires an intersection to be a basis open. `IsAmalgamation` says the actual
section on `V` restricts to each supplied section. `FamilySheafCondition` is
precisely existence and uniqueness of such amalgamations for compatible covers,
with an independent universe for the index type.

The chosen predicate `SheafCondition` quantifies over `BasisCover V`, whose
members form a set of basis opens. Its sections are indexed by the membership
subtype, which lies in the basis-open universe `u`. This gives one fixed
predicate suitable for a full subcategory. It does not restrict the source axiom:
`SheafCondition.family` proves gluing for a family indexed by **any** `Type w`,
without an index-size hypothesis. The proof constructs `rangeCover` by taking
the range of the family. For every range open, `rangeIndex` chooses one preimage
and `rangeSections` transports its section along equality of basis opens.
`restriction_transport`, proved by equality induction, shows this transport
commutes with restriction to a fixed smaller open. `Compatible.transport_eq`
applies compatibility on the common open itself and the identity restriction
law to identify duplicate sections. Consequently `rangeSections_at` recovers
each original section and `rangeSections_compatible` proves overlap compatibility
of the chosen representatives. Set-cover gluing then gives an actual section
restricting to every original section. Any second amalgamation restricts to the
same range sections and is equal by the set-cover uniqueness clause.

Conversely, `FamilySheafCondition.sheafCondition` applies source-family gluing
in universe `u` to the membership subtype of each set cover. Together with the
unrestricted forward theorem, `sheafCondition_iff_family` explains both directions
of the encoding. The range proof uses ordinary classical choice, not a universe
shrinking or smallness assumption.

Empty cases are included. `empty_family_covers_iff` says a family with empty
index type covers exactly an empty basis open. `emptyCover` constructs the empty
set cover, and `SheafCondition.isNormalized` applies its uniqueness clause to
show the raw value on empty is subsingleton. `normalized_empty_gluing` also
proves directly that a normalized presheaf glues an empty family uniquely to its
zero section, without assuming the other sheaf axioms. When empty is not in the
basis there is no empty basis object to which either requirement applies. Empty
spaces and empty bases are permitted wherever the actual basis condition permits
them.

`BasisSheaf B` is the full subcategory of normalized `Presheaf B` satisfying this
predicate. `sheafForget` is its actual fully faithful forgetful functor to
normalized presheaves. `sheafHomEquiv` identifies its morphisms with the actual
natural transformations of the underlying functors. Finally
`BasisSheaf.unique_gluing` exposes arbitrary-indexed unique gluing on bundled objects.

The set-cover encoding and all accompanying laws are derived intrinsic
formalizations of the source definitions, with no use of stalks, etale spaces,
basis extension, sheafification or their properties. Worker 595 implemented the
construction and laws; Worker 6 contributed the original-source audit,
full-subcategory packaging and the range/transport proof design.
