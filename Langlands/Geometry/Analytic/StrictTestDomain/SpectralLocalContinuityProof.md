# Local spectral continuity for actual rational quotient actions

Author: Worker 730.

This proof establishes the published
`RationalSpectralLocalContinuityStatement.{u,v}`. It is an internal consequence
of the Library's restricted rational spectral topology and actual rational
quotient action, as described in the paired statement Markdown.

The open positive-radius single-section test pulls back along the given
continuous homomorphism and the inclusion of the local subgroup. Its
neighborhood at one uniformly bounds displacement at every spectrum point.
At an arbitrary group element, translate to one and apply
`BanachSpectrum.SpectralBound.map` to the fixed bounded section automorphism.
The homomorphism law identifies the resulting displacement with the desired
difference.

For joint evaluation continuity, use half the positive tolerance for the
uniform displacement bound and half for continuity of evaluation of the fixed
section. The inequality `abs_sub_map_le_sub` for the multiplicative seminorm
and the real triangle inequality give continuity on the product. Finally,
compose joint evaluation with inversion in the local subgroup. The
homomorphism's inverse law gives the inverse-section evaluations of the
published spectrum action. The induced pointwise topology and continuity of
all coordinates then give joint continuity into the spectrum.

The proof uses no norm continuity of section orbits or uniform operator-norm
bound. It retains independent field and group universes and allows trivial
valuations, zero or nonreduced quotients, and empty loci or spectra. It makes
no comparison with the full analytic automorphism topology and adds no
quotient-norm, openness, gluing, or arbitrary-radius result. The underlying
source motivation is recorded in the imported statement Markdown; this
three-part internal implication is not asserted to be a verbatim literature
theorem.

The three generic continuity helpers are private to this proof module. They
work with an arbitrary homomorphism into bounded automorphisms, so that
transport can be checked without unfolding the constructed rational quotient
operators. The closing theorem supplies the subgroup's topological-group
structure by inducing it along the inclusion into `G`, and supplies the
helpers' displacement hypothesis using `eventually_spectralBound_one`.
No additional hypothesis appears in the closing theorem.
