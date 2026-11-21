# Ordered full finite level from a normalized Harris orbit

This internal construction applies the residue coordinates of the actual
Harris source, the global sections of the existing normalized invariant
level orbit, and the published `PolarizedFiniteLevel.FullLevel` definition.
It keeps the actual abelian scheme of the positive polarized datum. The base
is connected and locally noetherian, with a chosen algebraically closed
field-valued point; the other inputs are those of the actual finite torsion
and normalized level comparisons.

`harrisIntegralSource_rank` proves that the rank of the existing integer
lattice is twice `gH = [E : ℚ] n²`. Extending its integer basis to the
rational regular source identifies its rank with the rational dimension of
`A`. The finrank tower, the actual degree `n²` over `F` and the quadratic
degree of `F/E` give the formula. This is an arithmetic rank computation,
not a proof of the relative dimension of an abelian scheme.

Given an existing normalized invariant orbit at a level contained in
`K(m)`, `harrisIntegralOrderedFullLevel` maps the standard residue vectors
on `Fin (2 * gH)` through the reindexed source quotient isomorphism and
then through `harrisIntegralLevelSections`. The resulting ordered tuple
consists of actual global `m`-torsion sections. At the reference point,
evaluation agrees with the actual reduction of any normalized frame
representing the orbit, which is an additive equivalence with the actual
geometric `m`-torsion.

At any other algebraically closed field-valued point, the finite-étale
geometric path theorem supplies an isomorphism of the actual fibre
functors. The private restriction lemma proves that transport on the
multiplication-kernel cover carries the value of a fixed global section
at the reference point to its value at the other point. It uses naturality
with the section as a map from the identity cover, whose fibre is a
singleton. Thus the same ordered tuple has the coordinates of an additive
equivalence from the finite free residue module at every geometric point.
Additive homomorphisms between the residue modules preserve `ZMod m`
scalars, so taking the basis associated with that linear equivalence gives
exactly `FullLevel.full`. The path is used in this proof, not in the
selection of the ordered global sections.

This is a forward construction from an existing invariant orbit. It does
not compare changing the reference point and transporting the original
orbit, prove base-change naturality, characterize the image among ordered
levels, establish the polarization degree of an ordinary moduli datum, or
construct a representing scheme.
