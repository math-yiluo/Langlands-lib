# Factoring a finite morphism through a supplied quotient

Let `t, s : R → X` and `f : X → Y` be scheme morphisms with `t ≫ f = s ≫ f`.
When `f` is affine, for each point `x` of `X` the set of points `t(r)` with
`s(r) = x` lies in an affine open of `X`
(`exists_affine_open_of_equalizing_affine`). Choose an affine chart containing
`f(x)` and pull it back by `f`. This applies in particular to a finite `f`, and
supplies the affine-orbit hypothesis of the finite locally free equivalence
relation quotient theorem when the other hypotheses of that theorem hold.

Suppose a quotient `q : X → Q` is supplied and `t, s` present its kernel
pair as a pullback. If `q` is flat, surjective and quasi-compact,
`descendInvariantMap q hQ f hf` is the descended morphism `Q → Y`.
The factorization follows from the Mathlib regular epimorphism theorem for
such scheme morphisms and the displayed kernel-pair equality. It does not
construct the quotient or change the given relation.

`isFinite_of_surjective_precomp` says that if a separated locally finite
type map `g` becomes finite after precomposition with a surjective map `q`,
then `g` is finite. Universal closedness follows from the corresponding
composition rule, so `g` is proper. Each point fibre of `g` is the image
under `q` of a finite fibre of `q ≫ g`, hence finite. This gives local
quasi-finiteness and therefore finiteness. Consequently,
`isFinite_descendInvariantMap` gives finiteness of the descended morphism
when `f` is finite and the descent is separated and locally of finite type.

These are internal adapters from Mathlib's affine, effective epimorphism,
properness and quasi-finiteness interfaces. In the cubic separation route,
they apply to the invariant projective map of the complete linear system.
