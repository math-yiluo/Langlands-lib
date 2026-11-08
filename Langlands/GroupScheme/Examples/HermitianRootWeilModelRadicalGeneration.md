# Parabolic radical generation for actual Weil-restricted weighted Hermitian models

This internal unit transports `HermitianRootWeilAmbientGeneration` through an actual group-scheme isomorphism. It uses the original restricted source and the original maps on rational sections. The construction is derived from the unrestricted transport in `HermitianRootModelRadicalGeneration`; no external classification theorem is assumed or asserted.

Let `F`, `k`, and `L` be fields in an arbitrary common universe. Assume that `k/F` is finite and `L/k` is separable quadratic. The finite middle index lies in `Type`, the diagonal Hermitian form `H` has specified unit weights, and its middle form is anisotropic. There is no restriction on the characteristic or separability assumption on `k/F`.

For an actual isomorphism `e : A ≅ WeilSchemeModel.groupScheme F k L H w hw`, an actual morphism `a : A ⟶ G`, and a normal subgroup `N` of the rational points of `G`, containing the dynamic unipotent subgroup of the composed cocharacter forces `N` to contain the full rational image of `a`. The proof first applies the restricted model's full-image theorem to `e.inv ≫ a`, then evaluates it at the image of a rational point under `e.hom` and cancels the two isomorphism maps.

If the target `G` is connected reductive, its actual parabolic elementary subgroup contains those dynamics. `rationalPointsToParabolicElementarySubgroup` restricts the original rational map's codomain to that subgroup, and its coercion theorem is definitionally the original map.

Taking `a` to be the identity proves that a connected reductive group `A` equipped with the supplied isomorphism has `parabolicElementarySubgroup A = ⊤`. Consequently every subgroup containing the rational images of all its actual parabolic geometric unipotent radicals equals the full rational-point group. The latter conclusion does not require that subgroup to be normal; it uses the existing universal property of the actual parabolic elementary subgroup.

The supplied source isomorphism and the connected reductivity premise are retained. This unit does not construct a rank-one classification isomorphism, prove source geometric properties, or prove unrestricted local Kneser–Tits.
