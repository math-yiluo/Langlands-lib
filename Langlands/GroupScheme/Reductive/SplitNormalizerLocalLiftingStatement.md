# Local lifting of geometric normalizer points modulo a split torus

`SplitNormalizerGeometricLocalLiftingStatement` is the arbitrary-affine-base
local lifting input for the proof of Zariski-local Borel normalizer conjugacy.
It is a proposition target, not a proof or a construction of a Weyl quotient.

Let `R` be any commutative ring and `G` a reductive group over `S = Spec R`.
The closed coordinate torus `t : 𝔾ₘ^I → G` is maximal on every residue-field
fibre; a fixed root datum `P` on the coordinate lattices is realized on every
field-valued fibre; and all its root spaces are free of rank one. These are the
same split data used in `SplitBorelZariskiLocalConjugacyStatement`.

Given an algebraically closed field `k`, a point `x : Spec k → S`, and a point
`n` of the normalizer over `x`, there is an open neighbourhood `V` of the image
of `Spec k` and a normalizer section `nV` over `V`. An explicit morphism
`a : Spec k → V` over `S` records the factorization of `x`. The restriction of
`nV` differs from `n` by left multiplication by a torus point:
`(a ≫ nV) * n⁻¹ ∈ range t`. The normalizer is the full subgroup functor, tested
after every further scheme over the indicated test scheme. Range membership
also uses actual torus points, not only geometric-point membership in a closed
subset. All points in this statement are expressed over `S`; equivalently one
can use the canonical point equivalences for the corresponding pullback group
schemes.

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Proposition 5.1.6, p.138, identifies `N_G(T)/T` with the constant Weyl group of
the fixed root datum. Corollary 5.1.11, pp.142–143, proves surjectivity on
sections for the split group, using linked root-space trivializations and
reflection representatives. A geometric normalizer point determines a Weyl
element. Its corresponding constant section can be lifted (in particular,
Zariski-locally), with the same Weyl image on the geometric fibre; equality of
Weyl images says exactly that their quotient is a torus point. This is the
consequence invoked in the proof of Corollary 5.2.13(2), pp.158–159. Page
numbers here are both printed and one-based PDF page numbers.

No connectedness assumption is made on `Spec R`. The supplied field point
ensures that the base is nonempty in each application. The proof of Corollary
5.1.11 on p.143 treats locally constant Weyl-valued functions by their disjoint
open fibres; it does not require connected affine neighbourhoods. The already
published `AffineSplitNormalizerWeylStatement` concerns a connected nonempty
base and includes stronger global exactness and finite-subgroup assertions.
It does not by itself provide this input over arbitrary rings. No Borel
conjugacy or local equality assertion is included here.
