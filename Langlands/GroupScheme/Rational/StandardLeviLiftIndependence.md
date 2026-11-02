# Standard-Levi conjugate images are independent of the lift

This internal development proves the normalizer-lift independence used in the
second clause of `StandardLeviConjugationStatement`. It does not yet prove that
root-subset transport conjugates one standard Levi to another.

For any group scheme over any base, a base point in a subgroup functor gives a
point in that subgroup on every test scheme by restriction. Subgroup closure
then shows that its inner automorphism preserves the entire subgroup functor.
This is `SubgroupFunctor.comap_innerIso_hom_eq_of_mem`. Factoring a second base
point as `m = n * (n⁻¹ * m)` and using `innerIso_mul_hom`, `innerIso_inv_hom` and
`SubgroupFunctor.comap_comp` proves
`SubgroupFunctor.comap_innerIso_inv_eq_of_inv_mul_mem`: the two conjugate image
functors agree if the difference point belongs to the subgroup at the base.

For the actual quotient `relativeWeylGroup i`, `QuotientGroup.eq` puts this
difference in `centralizerPoints i`. The published equality
`torusCentralizer_carrier_base` and a containment `torusCentralizer i ≤ F`
therefore give `comap_innerIso_inv_eq_of_relativeWeyl_eq`. The construction
`relativeWeylConjugateSubgroupFunctor` descends these conjugate images to the
actual relative Weyl quotient by `Quotient.liftOn'`; its `_mk` theorem computes
the result at every lift. The specialization
`standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq` uses the published
`torusCentralizer_le_standardLevi`.

The specialization needs only affineness for the definition of `standardLevi`.
It holds for every subset of the character lattice, without reductivity,
maximal splitness or genericity. It is equality of subgroup functors on all
test schemes and imposes no root-transport condition. It does not equate the
maps on individual elements, which may differ by inner conjugation.

The proof is an internal algebraic consequence of the cited published
declarations. Its full-centralizer quotient and inverse-inner-automorphism
convention are those of the imported target. No new structural hypothesis is
introduced.
