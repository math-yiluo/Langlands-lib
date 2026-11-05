# Scalar extension of actual rational points as a group homomorphism

This derived interface specializes the published `baseChangeSectionHom` to an
extension of fields. Its inputs are fields `F` and `K` in an arbitrary universe,
an `F`-algebra structure on `K`, and an actual group scheme `G` over `F`.
The construction `geometricRationalPointHom` maps the group of actual `F`-points
of `G` to the group of actual `K`-points of its canonical base change.

The group law is inherited from `baseChangeSectionHom`, which restricts a section
and then applies the multiplicative pullback point equivalence. The theorem
`geometricRationalPointHom_apply` identifies this homomorphism with the existing
`geometricRationalPoint`: equality of the underlying maps follows from
`baseChangeSectionHom_left`, since both sections are the same pullback lift.
`geometricRationalPointHom_eq` records the corresponding function equality, and
`range_geometricRationalPointHom` identifies its range with the image of all
ground-field sections.

Assuming `HasDenseRationalPoints F G.X`,
`dense_geometricRationalPointHom` proves that the union of the images
of these extended sections is Zariski dense in the underlying
base-changed scheme. Its proof applies the published
`hasDenseGeometricRationalPoints_of_hasDenseRationalPoints` and rewrites each
section by the equality above. This assertion concerns the union of the images
of the sections as maps from `Spec K`; it is not a new topology on their index
group.

The interface has no finiteness, smoothness, reductivity, valuation, or
characteristic restriction. It retains ordinary rational density as an explicit
premise and does not prove density for any particular reductive group or the
spectral boundedness criterion.

The provenance is internal: this module only specializes and compares the
published section and geometric-point constructions. It provides the canonical
group homomorphism needed when the algebraic-closure and composition-factor
argument in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 2.2.11, printed pp.72–73 / PDF pp.103–104, uses the original group of
ground-field points after extending scalars. Neither the composition-factor
argument nor boundedness is asserted here. The November 2024 corrections,
Section 2.2, PDF p.24, impose Henselianity and restrict a topology comparison;
this purely algebraic section comparison and the published Zariski-density
extension theorem do not invoke that topology comparison.
