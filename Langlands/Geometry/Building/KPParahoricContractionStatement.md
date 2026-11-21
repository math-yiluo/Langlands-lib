# Parahoric conjugation into a contracting direction of an apartment

`Langlands.Geometry.Building.ParahoricContractionInApartmentStatement` is a
Prop-valued target for the contraction consequence of Kaletha–Prasad
Proposition 13.6.4 used in the geometric part of Proposition 13.6.7.

Take a nonarchimedean local field `F` of either characteristic, the connected
reductive `F`-group `G` and its actual maximal split torus `S → G` from
supplied `P : ParahoricBuildingData G`. Assume the apartment axioms
`P.SatisfiesApartmentAxioms`. Let `c` lie on no affine root hyperplane, so its
facet is a chamber, and let `x` lie in the closed chamber
`AffineRootSystem.facetClosure P.affineRoots c`. If `X ∈ Lie(G)` is contracted
by some `F`-cocharacter of `G` (the predicate `IsCocharacterNilpotent`), the
conclusion gives `p ∈ P.parahoricAt x` and an `F`-cocharacter `ν` of `S`.
The vector `Ad(p)X` lies in the strictly positive adjoint weight span for
`Gₘ → S → G` via `ν`. The group from which `p` is taken is the connected
parahoric of the supplied data, not the full point stabilizer.

## Source and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023),
§13.6.2 and Proposition 13.6.3, printed pp. 478–480 / PDF pp. 509–511,
set the chamber and contraction hypotheses. Proposition 13.6.4 and
Definition 13.6.5, printed p. 480 / PDF p. 511, supply the contraction
clause and its nilpotence convention. Proposition 13.6.7, printed p. 481 /
PDF p. 512, uses the parahoric conjugation and the resulting contracting
cocharacter of the apartment torus. The 1 November 2024 corrections,
p. 49, replace the last reference in §13.6.2 by Proposition 8.4.8(3).
This target does not use the special-fibre root-basis comparison in that
sentence.

The target is a derived weakening on supplied building data. It omits
compatibility of the cocharacter with the integral model at `x`
(Definition 13.6.1) and the nonnegative pairing conditions on `Δₓ` in
Proposition 13.6.4(2). It does not state the result for an arbitrary
rational representation, prove instability, or construct an apartment or
a parahoric model.
