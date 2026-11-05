# Weil restriction from an actual quasi-projective immersion

This is a derived construction for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed
pp. 9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad recalls existence of restriction of scalars for quasi-projective
schemes along finite locally free ring maps and uses finite-set affine
neighborhoods to reduce his local-field topology comparison to affine
schemes. This file supplies the geometric specialization of the existing
affine-chart representing construction from an actual projective immersion.
It proves no topology comparison.

The main declaration is `projectiveImmersionWeilRestrictionTestEquiv` in
`Langlands.AlgebraicGeometry.PointTopology`.

## Actual inputs and output

The rings `A` and `B` are arbitrary commutative rings in a common universe
`u`, with an actual `A`-algebra structure on `B` and instances
`Module.Finite A B` and `Module.Projective A B`. These are the finite
locally free hypotheses over the affine base. No field, separability,
characteristic, nonzero-rank, valuation or topological hypothesis occurs.

The target `Y` is an actual object of `Over (Spec B)`, with a locally
finite-type structure morphism `Y.hom`. Its additional data are a natural
number `n`, an actual morphism

```text
i : Y.left ⟶ ProjectiveSpace B n
```

with `IsImmersion i`, and the equality
`i ≫ projectiveSpaceToSpec B n = Y.hom`. Here immersion means locally
closed immersion. Projective space is the Library's actual polynomial
projective-space scheme. In particular a finite-type scheme with such a
relative projective immersion supplies these inputs. The construction
also works under the displayed weaker locally finite-type assumption;
it does not infer quasi-compactness of an arbitrary open immersion over
an arbitrary base ring.

Let `G = affineChartWeilRestriction A B Y`, the existing actual scheme over
`Spec A` glued from restrictions of all affine opens of `Y.left`.
For every actual scheme `T` over `Spec A`, the construction gives

```text
(T ⟶ G) ≃ (ringBaseChange A B T ⟶ Y).
```

There is no affineness, finite-type, separatedness or quasi-compactness
assumption on `T`. The forward map is exactly
`affineChartWeilRestrictionComparison`, namely actual base change followed
by the existing glued counit. Its inverse is the actual morphism glued
from affine local inverses in
`AffineChartWeilRestrictionRepresentability`. Both inverse laws are
inherited from that equivalence. The representing scheme and forward
comparison are the original ones, rather than an auxiliary representation
chosen from the projective immersion.

## Finite-set affine neighborhoods

The general helper
`hasFiniteAffineNeighborhoods_of_immersion_into_ample` takes an actual
immersion `f : X ⟶ Z` and an actual ample `Picard.LineBundle Z`. It proves
`HasFiniteAffineNeighborhoods X`: every finite set of actual underlying
scheme points of `X`, including the empty set, lies in one affine open.

For a finite set `E`, Mathlib factors `f` as the closed immersion
`f.liftCoborder` into the open `W = f.coborderRange`, followed by `W.ι`.
The finite image `f '' E` lies in `W`. The published
`Picard.exists_isAffineOpen_of_finite_of_ample` supplies an affine open
`V` of `Z` containing that image and contained in `W`. The preimage of
`V` under `W.ι` is affine because `V` is contained in its range; its
preimage under the closed immersion `f.liftCoborder` is affine as well.
The factorization identity identifies this open with `f ⁻¹ᵁ V`.
It contains `E`, giving the required actual affine-open neighborhood.
No ample line bundle on `X` or finite-set neighborhood premise on `X`
is assumed.

The specialization
`hasFiniteAffineNeighborhoods_of_projectiveImmersion` obtains an actual
ample line bundle on `ProjectiveSpace B n` from the published
`projectiveSpaceTwistOneAmple B n`, which proves ampleness of the actual
twisting bundle `𝒪(1)`. The general helper then applies to `i`.

## Separatedness and representing equivalence

`isSeparated_of_projectiveImmersion` proves `IsSeparated Y.hom`.
An immersion is a monomorphism and hence separated; the published proper
projective-space structure morphism is separated. Their composite is
separated, and the supplied equality with `Y.hom` gives the claim.
Relative separatedness is therefore proved from the input geometry.

`projectiveImmersionWeilRestrictionTestEquiv` installs this proved
separatedness and applies `affineChartWeilRestrictionTestEquiv` with the
proved finite-set affine-neighborhood property. Neither the neighborhood
property nor the desired representing equivalence is part of the inputs.

`projectiveImmersionWeilRestrictionTestEquiv_apply` records that the
forward map is exactly the canonical counit comparison.
`projectiveImmersionWeilRestrictionTestEquiv_natural` proves its
contravariant naturality for every morphism `f : T ⟶ S` of test schemes:
comparison of `f ≫ p` is actual base change of `f` followed by comparison
of `p`. The theorem
`projectiveImmersionWeilRestrictionTestEquiv_symm_natural` proves that the
inverse of base change of `f` followed by `q` is `f` followed by the
inverse of `q`. It uses the already proved naturality of the explicit
glued inverse.

## Scope retained

This unit establishes an actual all-test representing equivalence for the
displayed projective-immersion inputs. It does not prove finite type,
separatedness or quasi-projectivity of `G`, construct arithmetic models,
identify the local-field or adelic topologies, or construct the
finite-extension decompositions of the actual adelic rings. These remain
separate obligations of Example 4.2 and the whole-paper task.
