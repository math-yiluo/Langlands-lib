# Affineness of local isomorphisms over valuation domains

This internal construction proves the quasi-compact separated local-isomorphism
case over an arbitrary valuation domain `R`. It returns relative affineness of
`f : X ⟶ Spec R` and the actual canonical isomorphism
`valuationLocalIsoAffineIso : X ≅ Spec Γ(X, ⊤)`.

The proof does not establish that every etale morphism over the valuation ring
is a local isomorphism. That assertion would require additional conditions and
is not among the conclusions. In particular this is not a proof of the full
`ValuationRingEtaleAffinenessStatement`.

For an open immersion `Spec B ⟶ Spec R` with nontrivial `B`, the prime ideals of
`R` are linearly ordered. The open immersion reflects specialization, so prime
ideals of `B` are also linearly ordered. Two maximal ideals must therefore agree,
which proves that `B` is a local ring.

At any source point of a local isomorphism, restrict to an open on which the
map is an open immersion, then choose an affine open chart through the point.
Its composite with the map is an open immersion to the valuation spectrum.
The preceding argument makes its actual coordinate ring local. Thus the source
has an open cover by spectra of local rings. Quasi-compactness selects finitely
many members covering `X`.

The local isomorphism is etale and locally quasi-finite. Separatedness and
quasi-compactness let Zariski's main theorem embed `X` as an open subscheme of
its relative normalization, which is affine over the affine base. Thus `X` is
quasi-affine. The imported finite local-spectrum-family criterion makes `X`
affine, since the chosen finite family covers it. The actual canonical affine
model follows from the proved affineness.

The provenance is internal composition of Mathlib's local-isomorphism, valuation
ideal order, maximal-ideal, affine-chart and Zariski-main interfaces with
`isAffine_of_finite_localSpectrum_family`. No external-source proposition is
transcribed, and no noetherian, valuation-rank or group-scheme premise is added.
