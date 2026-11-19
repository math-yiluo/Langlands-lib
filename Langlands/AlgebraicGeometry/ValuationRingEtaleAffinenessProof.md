# Affineness of quasi-compact separated etale valuation schemes

Proof by Worker 606.

`Langlands.AlgebraicGeometry.valuationRingEtaleAffineness` has exactly the type
`Langlands.AlgebraicGeometry.ValuationRingEtaleAffinenessStatement.{u}`.
For every valuation domain `R` and every quasi-compact separated etale morphism
`X → Spec R`, its conclusion is that the morphism is affine. The valuation
domain and scheme are in the same arbitrary universe `u`.

The theorem installs the supplied geometric hypotheses as local instances and
applies `isAffineHom_etale_over_valuationDomain` from
`ValuationFpqcAffineModel`. That construction embeds `R` into an algebraically
closed field, factors this injection through a valuation subring by a local map,
and constructs a flat surjective map of valuation spectra. Torsion-free
flatness for valuation domains and flatness of a local homomorphism give its
faithful flatness. The etale pullback is affine by
`isAffineHom_etale_algClosedValuation`. Affineness descends along the fpqc cover,
so `X` is affine and its morphism to the affine base is affine.

The algebraically closed valuation theorem first proves that etale morphisms
over an integrally closed domain with algebraically closed fraction field are
local isomorphisms: monic standard-etale polynomials split over the base, and
their actual root sections are open immersions covering the source. A
quasi-compact separated local isomorphism over a valuation spectrum has a
finite cover by spectra of local rings. Zariski's Main Theorem makes the source
quasi-affine. An affine open containing the images of the charts' closed points
contains every point of the source, since each generalizes one of those images.

The statement's source discussion records a separate derivation from Temkin
and Tyomkin's results on Prüfer algebraic spaces.
[ValuationRingEtaleAffinenessStatement.md](ValuationRingEtaleAffinenessStatement.md)
