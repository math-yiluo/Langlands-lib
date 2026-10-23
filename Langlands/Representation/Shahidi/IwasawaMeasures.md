# Iwasawa measure compatibility in Shahidi's normalization

This derived prerequisite expresses measure item 4 on printed pages 76–77
of Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)* (1984). The smaller-group inclusion is displayed on
printed page 71. The original is registered as `shahidi-1984-fourier`,
SHA256 `a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

Lean's larger rank is n+1. `lastColumnUnipotent n x` is the actual matrix
with identity diagonal blocks and final upper column x, using the
published block-unipotent construction. Its zero, additive-composition
and upper-column entry formulas are proved from that construction.
The continuity proof composes the entrywise column map with the
published continuous block-unipotent map.

`iwasawaMeasureMap O n` sends the tuple ((x,a),z),k to

    u(x) diag(a,1) scalar(z) k.

Here a belongs to GL_n(F), z belongs to Fˣ, and k belongs to the actual
integral subgroup GL_(n+1)(O). This explicitly uses the last-column
unipotent before the smaller general linear block, the order for which
the source writes the inverse-determinant density. The standard rank
inclusion and scalar embedding are the published actual matrix maps.
Continuity follows by composing their continuity certificates with
projections and then multiplying. No decomposition or surjectivity
theorem is assumed to define this map.

`iwasawaCoordinateMeasure` is the product
((dn₂ × d*a) × d*z) × dk with density |det a|⁻¹.
`iwasawaMeasureFromFactors` is its actual measure pushforward under the
displayed multiplication map. `iwasawaMeasureFromFactors_apply` proves
the corresponding nonnegative integral formula for measurable sets,
assuming measurability of this multiplication map. The proof applies
the measure pushforward and density evaluation formulas. This unit
does not silently select independent Haar normalizations.

`IsIwasawaMeasureCompatible` is a Prop-valued relation on these supplied
measures and d*g. Its first equation is the actual weighted pushforward
identity of item 4. Its second is the displayed conclusion on page 77:
the d*g-volume of K equals the total dk-volume. The source's intervening
restriction dk′ concerns the subgroup G_n U_(n+1) Z_(n+1) intersected
with K. That subgroup restriction and its composition with the smaller
group, unipotent and central measures are not encoded here. In particular,
this relation records the compact-volume equality directly; it does not
assert an equality of restricted measures on every subset of K or derive
the volume equality without the other normalization conditions.

The measures are unbundled and the absolute value is supplied. Thus the
relations do not themselves assert Haar invariance, regularity,
local-field normalization or the existence of a compatible tuple.
The constructions work over a field with the indicated measurable
structures; the continuity results additionally use a topological ring.
In the intended local-field application O is the integer ring. The
measure dn₂ is already on its last-column coordinate space; compatibility
with a separately supplied measure on the actual radical remains a
transport condition. The pairing/quotient construction, compact-volume
and coordinate/Fourier equations, and the remaining radical conditions
belong to the full suitable-measure system. This module neither states
nor proves Theorem 5.1.
