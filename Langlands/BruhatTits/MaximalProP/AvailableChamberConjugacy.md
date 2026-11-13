# Conjugacy of actual chamber fixers

This internal construction concerns a supplied `KPBuildingDatum D` over a
nonarchimedean local field in an arbitrary universe `u`. Its main result
assumes only `D.SatisfiesGroupAxioms`: the actual pointwise zero fixers of
any two actual chambers are conjugate by an element of `D.base.zeroSubgroup`.
The equality is an equality of subgroups of the actual rational point group.

`exists_chamber_stabilizer_eq_conjugate_of_tits` works with the apartment
axioms and an explicit building Tits system. The facet correspondence first
places a Borel conjugate below the given chamber stabilizer. The empty type
is admissible, so the same correspondence realizes that Borel conjugate as
a facet stabilizer. Reverse inclusion of stabilizers makes the original
chamber precede that facet. The proved chamber maximality theorem
`eq_of_isChamber_of_facetPrecedes` identifies the two facets. Thus the
original chamber stabilizer is that Borel conjugate.

`exists_chamber_fixer_conjugator` obtains a reference apartment chamber
from the locally finite reflection arrangement and chooses the Tits system
supplied by the group axioms. Applying the preceding lemma to both chambers
expresses their stabilizers as conjugates by `gC` and `gE` of the same
Iwahori subgroup. Conjugation by `gE * gC⁻¹` therefore carries the first
stabilizer to the second. Subgroup image commutes with conjugation along
the zero-subgroup inclusion. The proved equality
`map_facetZeroStabilizer_eq_facetZeroFixer` converts the images of these
setwise stabilizers to the actual pointwise zero fixers.

`chamberFixerConjugator` chooses such an element and retains the ambient
subgroup equality in its subtype property. The conjugation convention is
forward conjugation, `g H g⁻¹`, as in `RelativeWeyl.conjugateSubgroup`.

The provenance is internal composition of the named Library constructions
and the Tits correspondence supplied in the hypotheses. No reductive
quotient comparison, pro-p theorem, normalizer theorem or additional
validity predicate is assumed or proved here. The module supplies the
geometric conjugacy input for the corrected KP Proposition 13.5.2 proof.
