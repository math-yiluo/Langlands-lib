# Represented conjugation-stable subfunctors of actual cocycles

This is a derived interface for the represented subfunctors used in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma A.8.13 and the proof of Proposition A.8.12, printed pp.553–554
(PDF pp.579–580). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
It uses the actual cocycles constructed in `AutomorphicAction.Cocycles`.

For an automorphic action `a` over an arbitrary base scheme `S`,
`a.CocycleModel` packages a scheme `X` over `S`, an actual universal
cocycle over `X`, and an injection from `X(T)` to actual cocycles over `T`
for every test scheme `T`. It also supplies an actual action of `G` on `X`,
whose cocycles transform by conjugation, and a base section corresponding
to the trivial cocycle. These are data and compatibility conditions.
The structure itself has no existence, finite-type, affineness, or
smoothness assertion.

`cocycle` restricts the universal cocycle to a parameter point.
Restriction compatibility makes `inclusion` a natural transformation
from the point functor of `X` to the cocycle functor. The field `injective`
requires this inclusion to be injective on every test scheme, including
nonreduced schemes. No comparison using only rational points is used.

`orbit` is the actual scheme morphism obtained by acting on the chosen
base section, and `actionRelation` is the morphism
`G × X → X × X`, `(g,x) ↦ (g • x,x)`.
`cocycle_comp_orbit` identifies the cocycle of every point of the orbit
with the canonical coboundary. Its proof uses equivariance, restriction
compatibility, and the basepoint's trivial-cocycle equation.
`orbit_fibers` then uses injectivity of the universal family and
`coboundary_eq_iff` to prove the full right-coset fiber equation:
`g` and `g'` have the same orbit image exactly when `g⁻¹g'` belongs
to the all-test fixed subgroup functor.

Over an arbitrary field, if `G` is smooth affine and the model is affine,
`homogeneousQuotient` applies the published
`HomogeneousQuotientFromEmbedding.quotientOfMapKernel`.
For every smooth closed representative `C → G` of the fixed functor,
it constructs a separated finite-type homogeneous quotient with smooth,
surjective, quasi-compact projection and the exact all-test coset fibers.
The proof rewrites the range of the representative as the fixed functor
and applies `orbit_fibers`. Affineness of the model implies its
separatedness, as required by that construction.

Affineness of the resulting quotient remains unproved here. Neither
existence of an affine finite-type cocycle model nor smoothness of its
action relation is supplied by this interface. Those are the further
geometric inputs in the source's argument.
