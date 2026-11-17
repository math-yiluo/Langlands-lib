# Extending rational maps from closed-point stalks

This is an internal construction for the semilocal step in
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4.
It derives a globalization interface from Mathlib's spreading-out and
rational-map APIs. It is not asserted as a separate quoted source theorem.

The imported `ValuativePartialMap.partialMap_fromFunctionField_eq_of_mem` from
[the published Anthropic FLT port](../AnthropicFLT/P2M/Sol/S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.md)
proves that a partial map from an
irreducible scheme restricts at its generic point by first restricting to
the stalk at any point of its domain, then applying the specialization
homomorphism from that stalk to the generic stalk.

For an integral scheme `X`, an arbitrary scheme `S`, and
`sY : Y ⟶ S` locally of finite type,
`rationalMap_mem_domain_of_stalk_extension` takes a rational map `r`
from `X` to `Y` and an `S`-morphism from the spectrum of the stalk of
`X` at `x` to `Y`. If its restriction to the function field agrees with
`r`, then `x` belongs to `r.domain`. The proof spreads out this stalk
morphism and uses equality at the generic point to identify the resulting
rational map with `r`.

`spec_open_eq_top_of_contains_maximal` proves that an open of a ring
spectrum containing every maximal ideal is the whole spectrum: every
prime ideal is contained in a maximal ideal, and opens are stable under
generization. Applying this to the preceding domain criterion gives
`rationalMap_domain_eq_top_of_closed_stalk_extensions`.

When the target is separated,
`rationalMapToHomOfDomainEqTop` turns an everywhere defined rational map
from a reduced scheme into an actual scheme morphism. The equation
`rationalMapToHomOfDomainEqTop_fac` identifies its restriction to the
domain with the canonical maximal partial map.
`rationalMapToHomOfDomainEqTop_toRationalMap` proves that it represents the
original rational map, and `rationalMapToHomOfDomainEqTop_comp` preserves a
given structure-morphism equation for the maximal partial map.
`morphismOfClosedStalkExtensions` applies this constructor to compatible
stalk extensions at all closed points of an integral affine source.

All declarations work in arbitrary universes. The closed-point extension
data and their agreement at the generic point are explicit hypotheses:
this module does not supply them from normal codimension-one points.
