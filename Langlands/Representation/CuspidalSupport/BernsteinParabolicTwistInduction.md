# Central scalars under induction from a represented parabolic

`BernsteinParabolicPresentation.TwistInductionScalarsAgree` compares the
scalar actions of two central elements for a represented parabolic `P = MN`
in a connected reductive group `G` over a nonarchimedean local field. Fix a
standard presentation of the actual triple. A cuspidal datum `a` of the
intrinsic standard family of `M` has an ambient datum `b` obtained by
transport across the inducing Levi isomorphism. If `χ` is an unramified
character for `a`, write `ω` for its transport to the inducing Levi of `b`.

Suppose `z_M` and `z` are central elements for `M(F)` and `G(F)` such that
inducing the component of `z_M` gives the component of `z` on the induced
object. If `z_M` acts on the intrinsic induction of the `χ`-twist by `c`
and `z` acts on the ambient induction of the `ω`-twist by `d`, then `c = d`.
The scalars are interpreted by `ActsByScalar` on the underlying smooth
representations at the common carrier universe `max u v`.

This is the comparison of evaluations along the map of cuspidal data in
Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, VI.7.3 (printed p. 185 / PDF p. 191) and VI.10.5
(printed p. 213 / PDF p. 219). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Proof

The actual Levi represents the standard Levi because its composite
inclusion is closed and its range is the standard Levi subgroup functor.
Both point identifications have the specified composite inclusion as their
ambient point map, so `leviPoints_eq` identifies them by extensionality.
Rewriting the standard comparison along that equality gives
`inductionObjIsoOfLeviPresentation` for every smooth inducing object.

`twistInduction_scalar_eq` uses linearity of represented induction and
induction compatibility to carry `c` to the component of `z` on the
represented induction of the intrinsic twisted object. Naturality along
`inductionObjIsoOfLeviPresentation` carries the same scalar to the literal
standard induction. The induction-in-stages isomorphism identifies that
object with direct ambient induction of the transported twisted inducing
representation. The pullback–twist isomorphism moves the twist to the
transported unramified character, giving the induction of the `ω`-twist of
`b`. Naturality preserves the scalar at both isomorphisms. The latter
induction is nonzero by `nontrivial_twistInduction`, so uniqueness of the
scalar gives `c = d`.
