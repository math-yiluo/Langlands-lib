# Uniform finite fibers of the standard Levi map on inertial classes

`StandardLeviInertialFiberBoundStatement` says that for a fixed
`BernsteinStandardFamily i ν`, there is a natural number `B` such that for every
standard Levi label `J` and ambient inertial class `s`, the fiber of
`standardLeviInertialToAmbient i ν family J` over `s` embeds in `Fin B`. The field
and representation-carrier universes are independent.

This bound is derived from the map on inertial classes in David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VI.7.3, printed p. 185 / PDF p. 191. It supplies uniform control on the number of
source components over an ambient component for the finiteness argument of
VI.10.5, printed p. 213 / PDF p. 219. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Proof

`standardLevi_exists_finite_normalizer_representatives` supplies a finite list
for each standard Levi `M_I`. It realizes `M_I` as the dynamic centralizer of a
cocharacter and identifies it with the centralizer of its split component. The
finite normalizer representatives for this torus centralizer then express every
rational point normalizing the embedded Levi as `g_t m` with `m ∈ M_I(F)`.

Choose a representative `a` of `s` with Levi `M_I`, and for each point of the fiber
choose a representative with Levi `M_K` and a rational conjugacy `c` from the Levi
of `a` to `M_K` witnessing ambient inertia. For a reachable `K`, fix one
conjugacy `c₀` depending only on `K`. The point of `c₀⁻¹ c` normalizes `M_I`,
so `c = c₀ g_t m` on rational points. Label the fiber element by `(K, t)`.

Two witnesses `c` and `d` with the same label satisfy `d = c m'` for some
`m' ∈ M_I(F)`. Thus the point of `d c⁻¹` lies in `M_K(F)`, hence in `M_J(F)`
since `K ⊆ J`. Transport of the original twists, using
`rationalInertiaRelated_pullback_iff` and `rationalIsoPullbackTransIso`, then
gives the relative inertia witness with conjugator `d c⁻¹`. Equality of labels
therefore gives equality in the relative quotient. If `N` is the maximum list
length over the finite set of standard Levi labels, the proof
`standardLeviInertialFiberBound` takes `B` to be the number of labels times `N`.
