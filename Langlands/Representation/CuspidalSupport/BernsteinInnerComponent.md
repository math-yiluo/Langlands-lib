# Component invariants inside a represented standard Levi

Let `D : BernsteinLeviPresentation i ν J j` present a closed connected
reductive representative `j : M ⟶ G` of a standard Levi. For a cuspidal
datum `a` of its intrinsic standard family, let `b` be the transported datum
and let `e` be the isomorphism of the inducing Levis. The point groups carry
their canonical topologies, with the local compactness and nonarchimedean
group hypotheses of the standard families. Local finite type supplies the
full rational unramified twists. The field and representation-carrier
universes are independent.

`BernsteinInnerComponentStatement` gives two comparisons. The affine Weyl
group of `b` for conjugation inside `M` is a subgroup of its affine Weyl
group for conjugation inside `G`. The intrinsic component algebra of `a` is
isomorphic over `ℂ` to the regular functions invariant under the first
group. The isomorphism preserves evaluation when the character is
transported along `e`, sending `χ` to `χ ∘ e⁻¹`.

`relativeLeviHom` composes the inverse of `innerLeviIso` with the intrinsic
inducing Levi inclusion. Its composite with `j` is the ambient standard
inclusion by `innerLeviIso_hom_comp`. Consequently a relative self-conjugacy
gives an ambient self-conjugacy with the same inducing Levi automorphism
and conjugating point in the image of `M(F)`. Conversely `D.points` lifts
any such ambient point, and monicity of `j` reflects the conjugacy
equation. The same twist multipliers then give the subgroup inclusion.

`conjugatePullback_iff` compares intrinsic association with ambient
association by points in that image. `rationalIsoPullbackTwistIso` identifies
the pullback of each twisted representation with the twist of the pulled
back representation by the transported character. The Weyl orbit
criterion therefore identifies invariant functions on both sides with
regular functions constant on the same associated twists. Restricting
`rationalUnramifiedRegularFunctionsEquiv e` to these subalgebras gives
`relativeComponentEquiv`, and the evaluation identity follows from the
evaluation identity for the full regular-function equivalence.

This comparison implements the component pullback used in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, VI.10.5 (printed p. 213, PDF p. 219). It uses the finite
quotient description in VI.7.1 (printed pp. 180–181, PDF pp. 186–187)
and the map on cuspidal data of VI.7.3 (printed p. 185, PDF p. 191).
The registered source is `renard-2026-representations-groupes-reductifs-padiques`
with SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
