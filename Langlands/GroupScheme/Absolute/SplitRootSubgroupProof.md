# Proof of the split root subgroup structure

The theorem `Langlands.GroupScheme.splitRootSubgroup` proves
`SplitRootSubgroupStatement.{u}` (module `Absolute/SplitRootSubgroupStatement`),
the formulation of Milne, *Algebraic Groups* (2017), Definition 21.10 and
Theorem 21.11(b)–(c). It keeps every hypothesis of the statement: `k` is an
arbitrary field in an arbitrary universe, `G` is a connected reductive group
over `Spec k`, `T` is a split torus, `i : T.toGrp ⟶ G` is a maximal torus and
`α ∈ roots i`. Containment is containment of subgroup functors on every scheme
test, and the given subgroup `H` need not be connected. The proof adds no
hypothesis on the characteristic or on perfectness of `k`.

## Root datum and the root line

`rootDatumExistence` (`Reductive/RootDatumExistence`, Milne 21.11 and 21.12)
gives a finite reduced root datum `P` on the character and cocharacter lattices
of `T` whose roots are `roots i`. The proof writes `α` as `P.root r`.
`RelativeRoot.hasNoHigherRoots_of_isRootDatumOf`
(`Reductive/IsogenyRootRestriction`) uses reducedness: no multiple `n • α` with
`n ≥ 2` is a relative root (`RelativeRoot.HasNoHigherRoots`).
`splitRootLieLine` (`Reductive/SplitRootLieLineProof`) gives a `k`-linear
equivalence `k ≃ₗ[k] weightSpace i α`.

## The additive parametrization

`exists_monic_rootRankOneRelations` (`Reductive/LinkedRootParametrization`)
gives a homomorphism `xp` from `VectorGroup.groupScheme (CommRingCat.of k) 1`
to `G`. It is monic, it is torus-equivariant for `α`
(`VectorGroup.IsTorusEquivariant i xp α`), and it is linked to a map for `-α`
by the rank-one relations. The first conjunct of the statement then follows
from three results:

- `HomImage.isClosedSubgroup_of_mono` (`HomImageEmbedding`): a monic
  homomorphism from a smooth connected affine group to an affine group
  locally of finite type is a closed subgroup. The one-coordinate vector
  group is smooth, connected and affine through its natural coordinates
  (`RelativeRoot.IsVectorGroupOfDimension`), and `G` is smooth and affine.
- `VectorGroup.IsTorusEquivariant.represents_root_of_lie_line`
  (`Rational/MonicRootParametrization`): a monic equivariant additive line
  represents `RelativeRoot.subgroup i α` on every test. Its inputs are the
  absence of higher roots and the root line.
- `VectorGroup.IsTorusEquivariant.lie_range_eq_weightSpace`: the image of
  `Lie.targetMapLinear xp k` is the whole of `weightSpace i α`. The
  differential is injective and the weight space is a line, so the image
  contained in the weight space has full dimension.

## The Lie containment criterion

Let `j : H ⟶ G` be a closed subgroup with `H` smooth, whose range is stable
under conjugation by `T`. By
`RelativeRoot.tangentSubmodule_eq_weightSpace_of_noHigherRoots`
(`Rational/RootPointLieEquiv`), the intrinsic tangent submodule of
`RelativeRoot.subgroup i α` equals `weightSpace i α`.

*Forward direction.* If the root subgroup is contained in the range of `j`,
then `RelativeRoot.tangentSubmodule_mono` (`Rational/TangentImage`) gives
containment of their tangent submodules. By the preceding equality, this is
the containment of `weightSpace i α`.

*Converse.* The private theorem `splitRootSubgroup_le_of_weightSpace_le`
proves it. Let `b` be the conjugation action of `T` on `G`, and let `c` be the
induced action on `H` (`AutomorphicAction.onRepresentedSubgroup`). Let
`A = RelativeRoot.cyclicTail α 1` be the semigroup of positive multiples of
`α`. Since `T` is split and `α ≠ 0`, no positive multiple of `α` is zero, so
`0 ∉ A`.

1. `RelativeRoot.weightFiltration_one_eq_subgroup`
   (`Rational/CyclicRootFunctorComparisonProof`) identifies the semigroup
   subgroup `RelativeRoot.semigroupSubgroup b A` with
   `RelativeRoot.subgroup i α`.
2. `RelativeRoot.semigroup_comap_eq_of_zero_not_mem`
   (`Rational/SemigroupZeroExcludedIntersection`) shows that the inverse image
   under `j` of `semigroupSubgroup b A` is `semigroupSubgroup c A`. This theorem
   requires `0 ∉ A` but not connectedness of `H`. The proof supplies its two
   structural premises with the published theorems
   `RelativeRoot.semigroupRealization` (`Rational/SemigroupRealizationProof`)
   and the second component of `CoordinateWeights.coordinateSemigroupComparison`
   (`Rational/CoordinateSemigroupProof`).
3. `RelativeRoot.isSmoothConnectedClosed_semigroupSubgroup`
   (`Rational/SemigroupRealizationGeometry`) shows that `semigroupSubgroup c A`
   is smooth, connected and closed in `H`. `RelativeRoot.IsSmoothConnectedClosed.map`
   (`Rational/SemigroupTransport`) carries this along the closed subgroup `j`.
   By `SubgroupFunctor.map_comap`, the image of the inverse image is the
   intersection `range j ⊓ RelativeRoot.subgroup i α`, so this intersection is
   smooth, connected and closed in `G`. The same theorem for `b` shows this for
   the root subgroup itself.
4. `RelativeRoot.tangentSubmodule_inf` computes the tangent submodule of the
   intersection as the intersection of the two tangent submodules. Since the
   tangent submodule of the root subgroup is `weightSpace i α`, the hypothesis
   makes the intersection equal to `weightSpace i α`. Thus the intersection and
   the root subgroup both have Lie image `weightSpace i α`
   (`RelativeRoot.hasLieImage_iff_tangentSubmodule_eq`).
5. `RelativeRoot.IsSmoothConnectedClosed.eq_of_le_of_hasLieImage`
   (`Rational/RepresentedLieUniqueness`) applies the full-Lie closed-subgroup
   theorem `lieSubgroupEquality` (`Lie/SubgroupEqualityProof`). A smooth
   connected closed subgroup functor contained in another one with the same
   Lie image equals it. So the intersection equals the root subgroup, and the
   root subgroup is contained in the range of `j`.

## Provenance

This is an internal deduction from Library results. It does not follow
Milne's proof of Theorem 21.11 step by step. The parametrization comes from
the linked rank-one maps of the root datum. Milne proves the containment
criterion with Proposition 16.64(a). Here the criterion is obtained
from the smooth connected semigroup model of the intersection and the
full-Lie subgroup equality theorem.
