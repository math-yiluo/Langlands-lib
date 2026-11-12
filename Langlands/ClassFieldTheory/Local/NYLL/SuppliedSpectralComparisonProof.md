# Supplied and spectral integer rings

Worker 93 authored this internal comparison for the finite inertia bridge in
Task 5239. It is derived from the existing supplied integer and spectral norm
constructions; it introduces no independent assertion attributed to literature.
The base and extension are arbitrary finite extensions of `Padic p` in independent
universes, with an actual compatible base-field embedding. Both supplied
realizations remain arbitrary.

`suppliedBaseSpectralIntegers F T` and
`suppliedExtensionSpectralIntegers F E T` abbreviate the existing spectral
valuation rings for the norm `LocalGalois.localNormedField F.Carrier` constructed
from the supplied base realization `T`. Their type-level instance choices are
exactly those used by the published `finiteInertiaSubgroup` construction.
No global instance is introduced.

The base subring equality `suppliedSpectralBaseIntegers_eq` is
`localNormedField_integer`. For the extension, both rings consist exactly of the
elements integral over the supplied base integer ring: the proof uses
`relativeIntegerStructure`, `integral_iff_mem_spectralIntegers`, and
`RingEquiv.isIntegral_iff` along the base equality. This proves the actual subring
equality `suppliedSpectralIntegers_eq`, rather than an abstract ring isomorphism
unrelated to field elements.

`suppliedSpectralBaseIntegerEquiv` and `suppliedSpectralIntegerEquiv` apply
`RingEquiv.subringCongr` to these equalities and hence preserve the actual field
elements. `suppliedSpectralIntegerEquiv_coe` records this coercion law.
`suppliedSpectralBaseResidueEquiv` and `suppliedSpectralResidueEquiv` are induced
on the actual residue quotients by `IsLocalRing.ResidueField.mapEquiv`; the two
`_residue` lemmas give their representative formulas.

`suppliedSpectralResidueEquiv_base` proves that these residue equivalences
commute with the actual relative residue map. Reducing a base residue class to
an integer representative leaves the same embedded field element on both
sides. `suppliedSpectralResidue_finrank` then transports the residue degree
using `Algebra.finrank_eq_of_equiv_equiv`, with the named
`relativeResidueAlgebra T S` installed on the supplied fields. No compatibility
of supplied valuations or rings is assumed.

The module imports existing published results by Lean name and uses environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).

The local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
