# Integral Weyl representatives and parabolic factorizations in each standard Levi of `GL_N`

`Langlands.BruhatTits.SpecialCompact.generalLinearIntegralLeviParabolics`
proves `GeneralLinearIntegralLeviParabolicsStatement.{u}` at arbitrary
universe `u`. For `GL_N` over a nonarchimedean local field `F`, a generic
diagonal cocharacter `ν` and a subset `J` of its simple relative roots, let
`M_J` be the actual standard Levi (`Standard.leviScheme`) with its closed
inclusion `j = Standard.leviHom` and factored diagonal torus
`iL = Standard.leviTorusHom`, and let `KJ` be the preimage of the standard
integral points `GL_N(𝒪_F)` under `j` on rational points. Then every class
of the relative Weyl group of `iL` has a representative in `KJ`, and for
every set `Q` of simple relative roots of `iL` the intersection of `KJ` with
the standard parabolic of `M_J` (for `iL`, `ν` and `Q`) is the product of
its intersections with the standard Levi and the standard unipotent radical,
in that order. This is Renard, Theorem V.5.1(5), as it applies parts (2) and
(3), for the standard integral subgroup of `GL_N`.
[Statement](GeneralLinearIntegralLeviParabolicsStatement.md)

## Implemented proof

**Ambient inputs.** The ambient theorem `generalLinearIntegralParabolics`
gives both properties for `GL_N` itself, the diagonal torus `i` and the
standard integral points `K`. Since `GL_N` is connected reductive and `i` is
maximal split, `StandardLeviNested.leviScheme_rankPackage` shows that `iL`
is maximal split in `M_J`, that the simple relative roots of `iL` for `ν`
are exactly `J`, and that for `Q ⊆ J` the standard parabolic, Levi and
unipotent subgroup functors of `iL` are the preimages under `j` of those of
`i`. By `Standard.isRepresentedBy_leviHom`, `j` is a monomorphism whose
range is the standard Levi of `i` for `J`; so the map `f` that `j` induces
on rational points is injective, and its image is the group of rational
points of that standard Levi, each of which lifts uniquely to `M_J`.
[Ambient Weyl representatives and factorization](GeneralLinearIntegralParabolicsProof.md)
[Nested standard Levis](../../GroupScheme/Rational/StandardLeviNestedTransport.md)
[Representability of the standard Levi](../../GroupScheme/Rational/StandardRepresentability.md)

**Weyl representatives.** Let `n` be a normalizing point of `iL` in `M_J`.
Because `iL` followed by `j` is `i` (`Standard.leviTorusHom_comp`),
`normalizerPointsMap` sends `n` to the normalizing point `f n` of `i`. The
ambient theorem gives an integral normalizing point `m` of `i` in the same
Weyl class, so `m (f n)⁻¹` is a rational point of the centralizer of `i`.
That centralizer lies in every standard Levi
(`centralizerPoints_le_standardLeviPoints`), so `m` lies in the standard
Levi of `i` for `J` and lifts to a point `m'` of `M_J` with `f m' = m`; in
particular `m'` lies in `KJ`. The image `m` lies in the normalizer subgroup
functor of `i` (`normalizerPoints_le_torusNormalizer`). The range of `i`
lies in the range of `j` (`range_le_standardLevi`), so the range of `iL`
followed by `j` is the intersection of the ranges of `j` and `i`, and
`SubgroupFunctor.mem_normalizer_of_range_comp_eq_inf` puts `m'` in the
normalizer subgroup functor of `iL`. As `iL` is a monomorphism,
`torusNormalizer_le_normalizerPoints` makes `m'` a normalizing point of
`iL`.
Finally, `weylAction_normalizerPointsMap` says that a normalizing point of
`iL` acts on the full character lattice of the diagonal torus as its image
in `GL_N` does. Since `m'` and `n` have images `m` and `f n` with equal
Weyl classes, they act on the character lattice in the same way, and the
faithfulness of the relative Weyl action of a split torus on its character
lattice (`IsSplitTorus.relativeWeylLatticeAction_injective`) shows that `m'`
and `n` define the same class.
[Normalizer transport](../../GroupScheme/Rational/RootKernelTorus.md)
[Normalizers of an intersection](../../GroupScheme/SubgroupFunctor/IntersectionNormalizer.md)
[Faithfulness](../../GroupScheme/Rational/RelativeWeylFaithfulness.md)

**Parabolic factorization.** Let `Q` be a set of simple relative roots of
`iL`; then `Q ⊆ J`, and on rational points the standard parabolic, Levi and
unipotent groups of `iL` for `Q` are the preimages under `f` of those of `i`.
For `g` in `KJ` and in the parabolic of `iL`, the point `f g` lies in `K`
and in the ambient standard parabolic, and the ambient factorization writes
`f g = m u` with `m` integral in the ambient standard Levi for `Q` and `u`
integral in the ambient standard unipotent radical. The ambient standard
Levi for `Q` lies in the range of `j`
(`StandardLeviNested.standardLevi_le_range_leviHom`), so `m` lies in the
standard Levi of `i` for `J`; hence so does `u = m⁻¹ (f g)`. Both lift to
`M_J`, the lifts lie in `KJ` and in the required preimages, and their
product is `g` by the injectivity of `f`. Conversely, a product of a point
of `KJ` in the standard Levi of `iL` and a point of `KJ` in its standard
unipotent radical lies in `KJ` and, by `standardLevi_le_standardParabolic`
and `standardUnipotent_le_standardParabolic`, in the standard parabolic.
[Standard parabolic subgroups](../../GroupScheme/Rational/StandardParabolic.md)

## Provenance and scope

The proof transports the ambient `GL_N` theorem to each standard Levi
through the named Library results; it does not follow Renard's argument
through the building. The theorem uses only the standard integral model of
`GL_N` and imposes no restriction on the characteristic or residue
characteristic of `F`, on `N` or on `J`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.
