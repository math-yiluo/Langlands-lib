# Basic-open and specialization geometry for valuation affineness

These internal helpers compose existing scheme and ring geometry. They do not
assert etale affineness over valuation rings, nor the host group-scheme
fibrewise-affineness target.

For any Bezout ring `R`, every quasi-compact open `U` of `Spec R` is an actual
principal basic open, and hence affine. The implemented proof uses Mathlib's
`PrimeSpectrum.isCompact_isOpen_iff_ideal` to write the open as the complement of
the zero locus of a finitely generated ideal. Bezout makes that ideal principal.
The zero-locus identities identify the original `U` with the basic open of its
generator. Valuation domains are among the rings to which this applies.

For an arbitrary quasi-affine scheme `X`, suppose a finite set `E` has the
property that every point `x` specializes to some member of `E`. Then `X` is
affine. The published
`OrbitSaturatedAffineOpen.exists_basicOpen_isAffineOpen_of_finite` gives an affine
basic open containing `E`. Every generalization of a point in this open belongs
to it, so the basic open is the entire scheme. The definition
`affineIsoOfFiniteSpecializationCover` constructs the canonical actual
isomorphism `X ≅ Spec Γ(X, ⊤)` from this proved affineness.

Finally, a finite jointly surjective family of morphisms from spectra of local
rings supplies such a finite set: take the images of the local closed points.
Any point of a local spectrum specializes to its closed point, and the given
morphism preserves specialization. Thus
`isAffine_of_finite_localSpectrum_family` proves affineness of a quasi-affine
scheme from that family. The family maps are otherwise unrestricted: they need
not be open immersions or affine. The finite index may be empty, covering the
empty scheme.

All schemes and rings remain in an arbitrary common universe. The provenance is
internal derivation from the cited imported Library finite-subset affine-open
construction and Mathlib's ordinary Bezout, spectrum, local-ring and
specialization interfaces. No external-source theorem is transcribed here.
