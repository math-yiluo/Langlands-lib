# Openness of a subgroup join from an open product map

This module reduces openness of the published unramified zero subgroup
`UnramifiedZeroDatum.zeroPoints` to two inputs. The first is openness of the
torus Iwahori subgroup `T(K)^0`. The second is openness of the product map
`C × T → H` on `K`-points. It proves neither input.

The content is internal. It is a general topological-group argument applied to
the published construction of Kaletha-Prasad, *Bruhat-Tits theory: a new
approach* (2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
The relevant construction is Definition 2.6.23(1), printed p.104 / PDF p.135:
over the maximal unramified extension `K`, `H(K)^0` is the subgroup generated
by the image `H(K)^♮` of `H_sc(K) → H(K)` and the torus Iwahori `T(K)^0` of a
maximally split maximal torus. The Library formalizes it as
`E.zeroPoints = E.simplyConnectedImage ⊔ E.torusIwahori.map (rationalPoints.map E.i)`,
where `E.simplyConnectedImage` is the range of `rationalPoints.map (E.π ≫ E.d)`.
This module uses those published definitions unchanged.

## Generic results

Throughout, `R` is a commutative ring, and `C`, `T`, `H` are group schemes over
`Spec R`. For morphisms `a : C ⟶ H` and `b : T ⟶ H`, the published
`subgroupProductMap a b : C.X ⊗ T.X ⟶ H.X` is the morphism `(c, t) ↦ a(c) b(t)`.

`comp_subgroupProductMap` proves that on an `R`-point `p` of `C.X ⊗ T.X` the
product map gives the product of the image of the first component under `a`
and the image of the second component under `b`. The proof is
`MonObj.comp_mul` together with the definition of `rationalPoints.map`.

`rationalProductPointMap a b` is the induced map on rational points,
`p ↦ p ≫ subgroupProductMap a b`, from the `R`-points of `C.X ⊗ T.X` to
`H(R)`. `rationalProductPointMap_apply` restates `comp_subgroupProductMap` for it.

`isOpen_range_sup_map_of_isOpenMap` assumes the following:

- `R` is a topological ring;
- `H.X.left` is affine, `H.X.hom` is locally of finite type, and `T.X.left`
  and `(C.X ⊗ T.X).left` are affine;
- `U` is a subgroup of `T(R)` that is open for `rationalPointTopology R T.X`;
- the map `rationalProductPointMap a b`, that is `p ↦ p ≫ subgroupProductMap a b`,
  is an open map from
  `rationalPointTopology R (C.X ⊗ T.X)` to `rationalPointTopology R H.X`.

Under these assumptions, the subgroup `(rationalPoints.map a).range ⊔ U.map
(rationalPoints.map b)` of `H(R)` is open.

The proof follows the implemented steps. Let `W` be the preimage of `U` under
the second projection `p ↦ p ≫ snd C.X T.X`. It is open because the published
`continuous_rationalPointMap` makes this projection continuous. The point
`lift 1 1` lies in `W`. By `comp_subgroupProductMap`, every point of the image
of `W` is `a(c) · b(t)` with `t ∈ U`, so the image lies in the join. The image of `W`
is open and contains the identity, so the join is a neighbourhood of the
identity. The published `rationalPoint_isTopologicalGroup` makes `H(R)` a
topological group, and Mathlib's `Subgroup.isOpen_of_mem_nhds` concludes that
the join is open.

The imported `PointTopology.tensor_isAffine` proves that the product over
`Spec R` of two objects with affine total spaces has affine total space. Its
proof identifies the categorical product with the pullback and applies
`IsAffine.of_isPullback`.

## Specialization to the unramified zero subgroup

Let `F` be a nonarchimedean local field, with the existing instances
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`,
and let `K = UnramifiedClosure F` carry `fixedFieldTopology F`. Let `H` be a group scheme over `Spec K` and `E : UnramifiedZeroDatum F H`
the published datum.

- `isAffine_cover` and `isAffine_ambient` prove that `E.C.X.left` and
  `H.X.left` are affine, from the affineness field of the connected reductive
  structures in `E.isSimplyConnectedDerivedCover`.
- `locallyOfFiniteType_ambient` proves that `H.X.hom` is locally of finite type,
  from smoothness of the connected reductive group `H`.
- `isAffine_coverTorus` proves that `(E.C.X ⊗ E.T.toGrp.X).left` is affine,
  using the datum's field `E.isAffine` for the torus.

`isOpen_zeroPoints_of_isOpenMap` takes `[IsAffine H.X.left]` and
`[IsAffine (E.C.X ⊗ E.T.toGrp.X).left]` as instance arguments. They are
propositions, so any proofs, for example the two lemmas above, may be
supplied. The theorem proves the following. Assume `E.torusIwahori` is open in
`rationalPointTopology K E.T.toGrp.X`, and assume
`rationalProductPointMap (E.π ≫ E.d) E.i`, that is
`p ↦ p ≫ subgroupProductMap (E.π ≫ E.d) E.i`, is an open map from
`rationalPointTopology K (E.C.X ⊗ E.T.toGrp.X)` to `rationalPointTopology K H.X`.
Then `E.zeroPoints` is open in `rationalPointTopology K H.X`.

The proof is `isOpen_range_sup_map_of_isOpenMap` with `a = E.π ≫ E.d`,
`b = E.i` and `U = E.torusIwahori`. Here `(rationalPoints.map (E.π ≫ E.d)).range`
is definitionally `E.simplyConnectedImage`. The topological-ring structure on `K` comes
from `fixedFieldValued F`, whose underlying topology is `fixedFieldTopology F` by
definition.

## Scope

The module does not prove that `T(K)^0` is open or that the product map is open
on `K`-points. Openness of the product map is expected from smoothness of
`C × T → H` together with a Henselian open-map theorem for smooth morphisms.
Neither is used here. The module also proves no compactness and no statement
over `F`.
