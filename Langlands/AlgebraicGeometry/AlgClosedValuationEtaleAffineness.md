# Etale affineness over algebraically closed valuation subrings

This internal construction proves that every quasi-compact separated etale
morphism `f : X ⟶ Spec A`, for a valuation subring `A` of an algebraically closed
field `K`, is affine. There is no rank or noetherian assumption. It constructs
the actual canonical model `algClosedValuationEtaleAffineIso : X ≅ Spec Γ(X, ⊤)`.

The implemented proof uses standard etale algebra charts. If every monic
polynomial over a base domain splits, Mathlib's standard etale local structure
at a source prime gives a principal localization with an actual standard etale
presentation. The imported split-standard-presentation theorem makes its
spectrum map a local isomorphism. These source neighbourhoods cover the source,
so the original spectrum map is a local isomorphism.

The next theorem passes from affine algebra charts to an arbitrary etale
scheme over an integrally closed domain with algebraically closed fraction
field. The imported monic-splitting theorem supplies splitting of every monic
presentation polynomial. Apply the preceding ring theorem on the scheme's
affine open cover and use source locality of `IsLocalIso`.

For a valuation subring of algebraically closed `K`, the field `K` is its
fraction field and the valuation domain is integrally closed. Thus the etale
map is a Zariski local isomorphism. The imported arbitrary-valuation
`isAffineHom_of_localIso_to_valuationSpectrum` proves affineness from
quasi-compactness and separatedness, and its actual affine model supplies the
canonical isomorphism.

The provenance is internal composition of the imported split-standard-etale
root sections, local-isomorphism valuation affineness, and Mathlib's etale
local structure and affine covers. This proves the algebraically closed
valuation-test input for the Weyl route. It does not by itself prove the full
arbitrary-valuation-domain statement or group-scheme fibrewise affineness.
