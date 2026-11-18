# Algebraically closed valuation covers and affine etale models

This internal construction supplies `AlgClosedValuationFpqcCover R` for every
valuation domain `R` in arbitrary universe `u`: an actual algebraically closed
field, a valuation subring of it, and a flat surjective morphism of its spectrum
to `Spec R`. Since both schemes are affine, this map is quasi-compact and gives
an actual fpqc cover. No rank, discreteness, noetherian or henselian condition is
assumed on the original valuation ring.

The construction takes the algebraic closure of the fraction field and applies
the existing local-ring valuation-factorization theorem to the injective map
from `R` into that field. The resulting map from `R` to the valuation subring is
local and injective. Its target is a torsion-free `R`-module. The imported theorem
that torsion-free modules over valuation domains are flat makes the map flat;
flatness and localness make it faithfully flat. The spectrum map is therefore
flat and surjective, as recorded in the constructed data.

For a quasi-compact separated etale morphism `f : X ⟶ Spec R`, pull back along
this actual fpqc cover. The imported
`isAffineHom_etale_algClosedValuation` proves that its source is affine.
`FaithfullyFlatAffineDescent.isAffine_of_isPullback` then proves the original
source affine. Its map to the affine base is affine as well. This proves
`isAffineHom_etale_over_valuationDomain` and supplies the actual canonical model
`valuationEtaleAffineIso : X ≅ Spec Γ(X, ⊤)`.

The provenance is internal composition of the actual algebraically closed
valuation-test construction, valuation factorization, torsion-free flatness,
faithful flatness and affine descent. It proves the full affine-model conclusion
for arbitrary valuation domains. It does not assert the unrelated host
group-scheme fibrewise-affineness theorem.
