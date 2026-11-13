# Maximal pro-p reduction and the positive normalizer

This internal construction works with the actual facet models, radical
preimages, parahoric reductions and point topology of a supplied
`KPBuildingDatum D`. It supplies a finite quotient adapter and a conditional
normalizer argument toward corrected KP Proposition 13.5.2.

`facetReductionSylow` takes the single-group axioms, a facet `Fa`, and a
subgroup `H` satisfying the existing
`IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H`. It also requires
`H` to lie in the actual zero fixer of `Fa` and the positive subgroup of
`Fa` to be pro-p. It constructs a Sylow subgroup of the actual reductive
quotient's residue-field points. Its underlying subgroup is precisely
the image of `H`, viewed inside the neutral integral-point image, under
`parahoricReduction`.

The pro-p discrete-image theorem proves the p-group property. For
maximality, any larger p-subgroup of the quotient lifts to an open pro-p
subgroup of the original rational-point group by the actual reduction
preimage construction. The lift lies in the zero subgroup because the
neutral integral points equal the facet zero fixer. It contains `H`, so
the given maximality identifies the lift with `H`. Surjectivity of
parahoric reduction then identifies the quotient subgroup with the image
of `H`. This proof does not assume that `H` contains the positive
subgroup at the start.

`normal_facetReductionSylow` additionally assumes that the facet zero
fixer normalizes `H`. Thus `H` is normal when viewed in the neutral
integral points, and surjective reduction carries that normality to the
Sylow subgroup of the whole quotient point group.

`isChamber_and_normalizer_eq_of_maximal` takes three explicit additional
mathematical inputs: `FacetReductiveComparisons D`, a proof of
`FiniteFieldNormalSylowTorusStatement`, and the pro-p property of every
facet positive subgroup. It takes a facet `C` whose positive subgroup is
maximal in the existing sense, and algebraic boundedness of that
subgroup's normalizer intersected with the actual rational common norm
kernel. Under these hypotheses it proves that `C` is a chamber and that
its positive normalizer in the zero subgroup equals its zero fixer.

The implemented argument first applies `positiveNormalizerFacet` to
obtain a face `N` of `C` with the given normalizer as its exact zero
fixer. This fixer contains and normalizes the positive subgroup of `C`,
so its reduction image is a normal Sylow by the preceding construction.
The explicit finite-group input makes the quotient of `N` a torus. The
explicit facet comparison makes `N` a chamber. The original face
relation and the chamber incidence equality then give `N = C`,
establishing both conclusions.

All results are at arbitrary universe `u`. The construction is derived
solely from the named Library interfaces and elementary subgroup
image/preimage arguments, so it introduces no external source claim.
The finite normal-Sylow theorem, facet comparison, boundedness and facet
pro-p inputs remain explicit premises of this intermediate result.
This module does not prove `AvailableMaximalProPStatement` or assert
that an unproved Library proposition is available as a theorem.
