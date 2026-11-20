# Galois truncation quotients through a transitivity index

This module proves `Langlands.Ramification.Kummer.truncationGaloisQuotient`
with type `TruncationGaloisQuotientStatement.{u}`. Write `G_K^y` for the
absolute upper group of a p-adic field `K` at the real index `y`.

The transitivity hypothesis and normality of `G_F^μ` write each element of
`G_F` as a product of an element of the fixing subgroup and an element of
`G_F^μ`. The range theorem for `intermediateGaloisMap` lifts the first factor
to `G_E`. Antitonicity puts the second factor in `G_F^x` for `x ≤ μ`. Thus
every class of `G_F/G_F^x` is represented by the image of an element of `G_E`.

The private proof for a continuous Galois homomorphism `ι` uses
`QuotientGroup.liftEquiv` on the composite of `ι` with the target quotient
map. The published `truncationGaloisComap` identifies its kernel with `G_E^x`
in the intermediate-field application. The representative property makes the
composite surjective. The induced equivalence carries `mk a` to `mk (ι a)`
and is continuous by the source quotient topology. Mathlib's Krull-topology
compactness theorem gives compactness of the source absolute Galois group and
hence of its quotient. The target quotient is Hausdorff by closedness and
normality of `G_F^x`. The continuous equivalence therefore has a continuous
inverse.

For each `-1 ≤ y ≤ x`, the comap equality at `y` gives the forward inclusion
of filtration images. In the reverse direction, write an element `g` of
`G_F^y` as `ι a * n` with `n` in `G_F^x`. Since `G_F^x ≤ G_F^y`, the element
`ι a = g * n⁻¹` belongs to `G_F^y`. The comap equality puts `a` in `G_E^y`,
and `ι a` and `g` have the same class modulo `G_F^x`. This proves equality
of the images on the whole interval specified in the statement.

The kernel and surjectivity steps are the absolute-Galois form of the
argument in the operator's *Numerical local Langlands for GL_n, counts on
the two sides and the recommended route* (16 November 2026), Lemma
`lem:trunc`, lines 876–889 of `numerical-LLC-route.tex` (registered source
`operator-numerical-llc-route-2026-11-16`). The proof uses the absolute upper
groups and index range of the published statement and adds the quotient
topology and filtration arguments above.
