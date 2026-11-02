# Scheme morphisms for conjugation on dynamic unipotent subgroups

Let `G` be a group scheme over any scheme `S`, let `χ : G_m → G` be an actual
cocharacter, and suppose the published dynamic subgroup functors `P(χ)` and
`U(χ)` are represented by homomorphisms `iP : P → G` and `iU : U → G`.
The dynamic definitions use orbit extension on every test scheme, including
nonreduced schemes.

This module constructs the morphism of schemes over `S`

`parabolicConjugation hP hU : P ×_S U → U`.

Its composite with `iU` is the ambient conjugation morphism
`(p,u) ↦ iP(p) iU(u) iP(p)⁻¹`. It is unique with this property and gives the
natural action of `P(T)` on `U(T)` by group automorphisms on every test `T`.
There is no separatedness, smoothness, affineness, finiteness or field
hypothesis. Representation of these particular subgroup functors is an
explicit hypothesis in the general construction.

## Provenance and proof

This is an internal specialization of `SubgroupFunctor.normalizedConjugation`
and its proved action laws. It reuses the published theorem
`Dynamic.unipotent_isNormalizedBy_parabolic`, not an additional structural
claim from the literature. That theorem multiplies actual orbit extensions:
if `p` has limit `l` and `u` has limit `1`, the conjugate has limit
`l · 1 · l⁻¹ = 1`. Neither the existence of a representing normalizer nor the
existence of a quotient is used.

`range_unipotent_isNormalizedBy_range_parabolic` transports the published
normalization theorem through the range equalities in `hP` and `hU`.
`parabolicConjugation` is the factorization of the universal conjugation
morphism given by that normalization condition.
`parabolicConjugation_comp` and `lift_comp_parabolicConjugation_comp` record
its defining equation and its value after the inclusion on every pair of
test points. The monomorphism in `hU` gives `parabolicConjugation_unique`.
`parabolicConjugation_naturality` records restriction of points.
`parabolicConjAction hP hU T : P(T) →* MulAut U(T)` bundles the action;
`parabolicConjAction_apply` identifies its value with the same scheme
morphism. Thus both the action laws and invertibility concern the actual
represented subgroup.

## Concrete block schemes in GL

For any finite index type `n`, commutative ring `R`, and arbitrary integer
weights `e : n → ℤ`, the second section uses the published quotient schemes
`blockParabolicScheme n R e` and `blockUnipotentScheme n R e`, and their
published closed inclusions into `GeneralLinear.groupScheme n R`.

`range_blockUnipotent_isNormalizedBy_range_blockParabolic` follows from
the published full-functor equalities
`unipotent_diagonalCocharacter` and `parabolic_diagonalCocharacter` and
the published representations of the block subgroup functors.
`blockParabolicConjugation n R e` is therefore an unconditional morphism
between those concrete schemes. It has the ambient conjugation formula
(`blockParabolicConjugation_comp`,
`lift_comp_blockParabolicConjugation_comp`) and is natural in the test
scheme (`blockParabolicConjugation_naturality`).

`pointsEquiv_blockParabolicConjugation` shows that applying the published
GL point equivalence gives ordinary conjugation in
`GL_n(Γ(T, 𝒪_T))`. The proof applies that multiplicative equivalence to
the ambient formula. `blockParabolicConjAction` bundles the resulting
action by automorphisms, with the identical underlying scheme morphism
as recorded by `blockParabolicConjAction_apply`.

No ordering or distinctness of weights, nontriviality of `R`, or positive
rank is required. The empty index type is included. No topology, Haar
measure, representability of a general normalizer, or assertion about
quotients of points is made.
