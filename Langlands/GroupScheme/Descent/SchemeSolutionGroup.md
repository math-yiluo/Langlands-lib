# Group structure on an underlying scheme solution

For schemes `B,S` in any universe `u`, a surjective étale map `p : S ⟶ B`,
an actual group scheme `G` over `S`, and `D : Datum p G`, this module
constructs `s.solution : Solution D` from a supplied
`s : SchemeSolution D`. The input supplies an actual quotient scheme,
projection, pullback square and relation invariance. There are no
affineness, quasi-compactness, field, smoothness, finite-type, or
commutativity assumptions.

This is an internal generalization of the reconstruction part of
`AffineDatumGroup`. Its inputs are the compatible-section equivalence
in `SchemeSolutionSections`, the group-preserving transport in
`SectionTransport`, and Mathlib's group transfer and represented group
object APIs. It introduces no external literature assertion or axiom.

`sectionGroup U` transfers the compatible-section subgroup's group
structure across `s.sectionEquiv U` to the actual maps `U ⟶ s.obj`.
The local-section formulas identify its unit and product. Pullback
functoriality gives `localSection_comp`. The injectivity of restriction
then proves that precomposition preserves unit and product. Consequently
`sectionPresheaf` is a group-valued presheaf on `Over B`. Its underlying
set-valued presheaf is represented by `s.obj`, using the identity hom-set
equivalence. Mathlib's `GrpObj.ofRepresentableBy` constructs `groupObj`
and hence `groupScheme` on that same object, with actual scheme morphisms
as its group operations.

The represented group-object Yoneda isomorphism identifies the resulting
section operations with the transferred operations.
`iso_isMonHom` checks the unit and multiplication laws for the original
slice pullback comparison: the operations of monoidal pullback are its
monoidal comparisons followed by pullback of the original operations.
Restriction carries the reconstructed unit to the local unit and the
reconstructed multiplication to the local product. The two monoidal
product projections give the required multiplication equation.
`groupIso` bundles the resulting actual group-scheme isomorphism; its
underlying maps are exactly `s.iso.hom` and `s.iso.inv`.

`compatible_of_proj` proves that any such homomorphism preserving the
quotient projection respects the canonical datum and `D`. Compare the
two maps into the second pullback of `G`. Their base projections agree
because both are slice morphisms. The supplied quotient pullback square
reduces equality of their original-group projections to equality over
`S` and after `s.proj`. The former follows from the slice equations; the
latter follows from relation invariance, preservation of the quotient
projection, and the canonical overlap projection formula.
`groupIso_compatible` applies this criterion to `groupIso`.

Finally `solution` supplies the actual descended group, pullback
isomorphism, and compatibility on the original overlap required by the
published `Solution` structure. Its underlying object is the supplied
`s.obj`. Constructing `SchemeSolution D` for an arbitrary affine
group-scheme datum over an arbitrary base remains a separate gluing
obligation. This module does not by itself prove the host quasi-split
inner-form existence theorem.
