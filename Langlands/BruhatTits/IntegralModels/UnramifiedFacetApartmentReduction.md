# Apartment reduction for actual descended facet models

This is an internal deduction from published building, zero-fixer and model
transport results. It supplies apartment coordinates for the parabolic-image
argument; it does not assert parabolicity or a reduction-preimage equality.

Work over a nonarchimedean local field `F`, at arbitrary universe `u`. Let `B`
be valuation building data for an affine `F`-group `G`, and let `C` be maximal
unramified building data for the actual extension of `G` to
`inertiaFixedField F`. Supply a map `e` of reduced buildings, an affine
apartment map `a`, equivariance for actual rational-point extension, apartment
compatibility, and the exact restricted-facet identity

`a ⁻¹' facet C.affineRoots (a x) = facet B.affineRoots x`.

The first helper places the image under `a` of each full apartment facet in
one full upstairs apartment facet and proves that this image is nonempty.
The second identifies the image under `e` of every translated apartment
subset with the translate, by the extended original group element, of its
affine image under `a`.

For incident downstairs building facets `Fc ≺ Fc'`, supply a zero datum `E`,
two actual integral models `N`, `N'` over `fixedFieldIntegers F` characterized
by the zero fixers of `e '' Fc.val` and `e '' Fc'.val`, and an actual morphism
`ψ : N'.Hom N (𝟙 _)`. The main theorem produces a single original rational
group element `g`, two nonempty upstairs apartment subsets `Ω`, `Ω'`, and
containing upstairs facets `Fa`, `Ca`. It records their translated images
under `e` exactly. Transporting both models by the inner automorphism of
the inverse of the extended `g` identifies their actual integral-point
images with the zero fixers of `C.apartmentMap '' Ω` and
`C.apartmentMap '' Ω'`. It also proves `Fa` is a face of `Ca`.

The proof unpacks the common chart already present in `FacetPrecedes`.
The restricted-facet identity gives the two containing facets. The published
`integralPoints_transport_innerIso` and `unramifiedZeroPointsIndependence`
give the two model characterizations after transport. Transporting `ψ`
gives inclusion of the actual integral-point groups. Applying
`UnramifiedZeroDatum.isFaceOf_of_zeroFixer_le` to that inclusion gives the
claimed upstairs incidence.

`incidentApartmentTranslation` chooses the original rational group element
from this existence theorem. Unfolding it and applying `Classical.choose_spec`
to `exists_incident_apartment_models` supplies the other coordinates and all
the displayed properties for that translation.

No independent assumption that `a` preserves face incidence is used. The
upstairs incidence conclusion depends on the supplied model morphism.
Smoothness, connectedness, parabolicity and generation are not hypotheses
or conclusions of this unit.
