# Smooth integral models from actual affine descent data

This internal construction turns an affine solution of an actual group-scheme
Čech datum into a smooth integral model, retaining a prescribed generic
identification. It is a structural step toward the proof of Kaletha–Prasad
Fact 2.10.16, not a proof of that fact.

## Inputs and scope

All types lie in an arbitrary universe `u`. The rings `R` and `A` are domains
with specified fraction fields `K` and `L`. Their coefficient maps form the
commuting square required by `IntegralModel.baseChange`. The spectrum map
`Spec A → Spec R` is flat and surjective; it is automatically quasi-compact.

The inputs are a group scheme `G` over `K`, a smooth integral model `N` of
`G_L` over `A`, an actual datum `D` on `N.group`, and a solution `s` of `D`
whose descended group has affine underlying scheme. The generic identification
`e : s.obj_K ≅ G` is supplied. For example, the published
`Datum.affineSolution` supplies `s` and its affineness. This module does not
construct a datum from a family of Galois automorphisms or construct `e`.

## Construction and proofs

`Descent.Solution.smooth` works over arbitrary schemes: a solution's actual
pullback is isomorphic to the supplied upstairs group. Its structure map is
therefore smooth when the upstairs structure map is smooth. Mathlib's fpqc
descent of smooth morphisms then gives smoothness of the downstairs structure
map.

`IntegralModel.ofAffineSolution s hN e` uses `s.obj` as the group and `e` as
the specified generic isomorphism. Affineness of the group and the affine
integral base give affineness of its structure map. Descended smoothness gives
flatness and local finite type, so this is the published `IntegralModel`
structure with all its required properties. `isSmooth_ofAffineSolution`
records smoothness of that actual model.

`isoOfAffineSolution` takes the equation asserting agreement of the supplied
generic identifications with the generic fibre of `s.iso`. It packages
`s.iso` as an `IntegralModel.Iso` over the identity of `G_L`.
`integralPoints_ofAffineSolution` applies the published
`Iso.integralPoints_eq`, showing that coefficient extension of this model has
exactly `N.integralPoints`.

## Provenance and remaining obligations

These are internal consequences of the published affine group-datum
effectivity and coefficient base-change APIs and Mathlib's fpqc descent for
smoothness. No separate source theorem is claimed. The use in Fact 2.10.16
still requires constructing an actual datum from the Galois-stable integral
points and descending the generic comparison; neither is an assumption added
to the target statement by this module.
