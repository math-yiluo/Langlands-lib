# Scheme geometry of a compact represented saturation

This internal adapter converts a compact scheme representation of an
actual local-image saturation into the scheme base-change data used for
effective descent. It uses `EtaleImageSaturation`, `CompactLocalImage`,
and `RepresentedLocalImageGeometry`. The universe `u` is arbitrary.

Let `e : B → T` be etale, and let actual fppf sheaves `G` and `F` fit
into a cartesian presheaf square with projections `π : G → F` and
`p : G → h_B`, and bottom arrows a monomorphism `f : F → h_T` and
`h_e`. Suppose `a : h_V → G` is an open immersion with structure map
`w : V → B`, so `a ≫ p = h_w`, and suppose `w` is locally of finite
type. Write `A` for the fppf local image of `a ≫ π`. The explicit
remaining hypothesis is that `A.preimage π` is represented by a compact
scheme over the fixed base.

`SaturatedLocalImageGeometry e f (a ≫ π)` records an actual compact
scheme `W`, a map `q : W → B`, and a map `k : h_W → A` such that their
square over `A.ι ≫ f` and `h_e` is cartesian. The map `k` is locally
surjective for the fppf topology. The scheme map `q` is a monomorphism,
locally of finite type, and locally quasi-finite.

The theorem `saturatedLocalImageGeometry` constructs this data from
the stated hypotheses. The inverse-image/local-closure identity and
`translate_isPullback` identify the given saturation with the local
image of `translate`. The transported chart is etale by base change,
and `newBase` is locally of finite type by its scheme pullback square.
`RepresentedLocalImageGeometry` then gives the scheme map `q` with its
three geometric properties. The representation followed by the
saturation inclusion has exactly that saturation as its range. Its
map to `F` lifts into `A`; the cartesian range criterion and vertical
pasting give the required square. Finally, the canonical locally
surjective map `h_V → A` lifts through `k` by the saturation square,
so local surjectivity passes to `k`.

The compact representation of the saturation is an explicit input;
no scheme representation of `A`, effective descent theorem, or final
schemehood statement is assumed or concluded.
