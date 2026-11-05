# Openness of the actual zero subgroups from norm and product smoothness

This module proves `ParahoricBuildingData.isOpen_centralizerZero`. For every
`P : ParahoricBuildingData G` it shows that the actual subgroup
`P.centralizerZero` is open in `rationalPointTopology F P.centralizer.Z.X`. The
local instances are exactly those of the published target
`CentralizerZeroCompactOpenStatement`, so this is the openness conjunct of that
target. The theorem has two hypotheses, the published statements
`DerivedCoverTorusProductSmoothStatement.{u}` and
`GaloisNormSmoothnessStatement.{u}`. Neither is proved here. The module proves
no compactness, so it does not prove `CentralizerZeroCompactOpenStatement`.

## Provenance

The content is internal. It assembles published Library results along the
route of Kaletha-Prasad, *Bruhat-Tits theory: a new approach* (2023), registered
as `kaletha-prasad-2023-bruhat-tits-new-approach`.

- Lemma 2.5.12 (printed pp.89-90 / PDF pp.120-121) says that the image of
  `T(L)^b` under the norm `T(L) → T(K)` is open. The book's reason is that this
  norm is the map on `K`-points of the algebraic norm `R_{L/K}(T_L) → T`, which
  is smooth and surjective. Definition 2.5.13 (printed p.90 / PDF p.121) calls
  this image `T(K)^0`.
- Definition 2.6.23 (printed p.104 / PDF p.135) defines `H(K)^0 = H(K)^♮ · T(K)^0`
  for quasi-split `H` (part 1), and `Z(F)^0 = Z(K)^0 ∩ Z(F)` when `Z` is
  anisotropic modulo its center (part 2). The Library formalizes these as
  `UnramifiedZeroDatum.zeroPoints` and `anisotropicZeroPoints`.
- Lemma 2.6.24 (printed pp.104-105 / PDF pp.135-136) states that the group is
  open. Its proof derives openness from openness of `T(k)^0` and Fact 2.6.22.

The Lean proof follows Lemma 2.5.12 for `T(K)^0`. For `H(K)^0` it does not use
Fact 2.6.22. It uses instead that the product map `C × T → H`, from a simply
connected cover `C` of the derived subgroup and the torus `T`, is smooth, so it
is open on `K`-points. Openness then descends to `F` through the continuous
extension of scalars `Z(F) → Z(K)`.

## Setting

Let `F` be a nonarchimedean local field with the existing instances
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`,
and let `K = UnramifiedClosure F` carry `fixedFieldTopology F`. Let `H` be a
group scheme over `Spec K` and `E : UnramifiedZeroDatum F H` the published
datum. Write `L = E.L` for its finite Galois splitting field inside `F^sep`, and
`T_L = GaloisPointComparison.baseChanged K L E.T.toGrp` for the base change of
the torus, which `E.isSplitTorus` says is split. `L` carries the topology of
`Valued.mk' (intermediateValuation F L)`.

## Support lemmas

- `isAffine_splitTorus` proves that `T_L.X.left` is affine. The proof applies
  `isAffine_of_isAffineHom` to the affine structure morphism supplied by
  `E.isSplitTorus.isAffineHom`.
- `locallyOfFiniteType_splitTorus` proves that `T_L.X.hom` is locally of finite
  type, from smoothness of the split torus.
- `moduleFree_splittingField` and `moduleProjective_splittingField` prove that
  `L` is a free and a projective `K`-module, by `Module.Free.of_divisionRing`
  and `Module.Projective.of_free`. They are declared as local instances because
  the generic instance search for these classes on `L` times out.

## The bounded subgroup on the Weil restriction

In this section `T_L.X.left` is assumed affine and `T_L.X.hom` locally of finite
type, as instance arguments. The support lemmas above supply both. Write
`R = AffineWeil.groupScheme K L T_L` for the Weil restriction, and
`e = GaloisNorm.rationalPointsEquiv K L E.T : T_L(L) ≃* R(K)` for the published
identification.

- `weilKernel` is the image under `e` of
  `characterValuationKernel (intermediateValuation F L) T_L`. That subgroup
  consists of the points of `T_L(L)` at which every `L`-rational character has
  valuation `1`. The published `torusNormIwahori` uses it as `T(L)^b`.
- `torusIwahori_eq_map_weilKernel` proves
  `E.torusIwahori = E.weilKernel.map (rationalPoints.map (GaloisNorm.norm K L E.T))`.
  By definition `E.torusIwahori` is the image of the same kernel under the
  published `GaloisPointComparison.rationalNorm`. After `Subgroup.map_map`, the
  two homomorphisms agree pointwise by the published
  `GaloisNorm.norm_rationalPoints`.
- `rationalPointsEquiv_symm_eq` proves that the inverse of `e` is the explicit
  composite
  `x ↦ (rationalCoeffEquiv L T_L).symm (basePointsEquiv K L T_L (rationalCoeffEquiv K R x))`.
  The proof unfolds `e` and simplifies with `MulEquiv.symm_trans_apply` and
  `MulEquiv.symm_symm`.
- `coe_weilKernel` proves that, as a set, `weilKernel` is the preimage of the
  kernel under the inverse of `e`. The proof is
  `Subgroup.map_equiv_eq_comap_symm'`.
- `isOpen_weilKernel` proves that `weilKernel` is open in
  `rationalPointTopology K R.X`. The kernel is open in
  `rationalPointTopology L T_L.X` by the published
  `isOpen_splitCharacterValuationKernel`. The composite above is continuous by
  the published `AffineWeil.continuous_rationalBasePoints_of_continuousSMul`.
  That theorem needs `ContinuousSMul K L`, supplied by the published
  `intermediateValuation_continuousSMul`, and continuous addition on `L`, which
  holds for the valued topology. The theorem rewrites with `coe_weilKernel` and
  `rationalPointsEquiv_symm_eq` and takes the preimage.

## Openness over `K`

`isOpen_torusIwahori` assumes `GaloisNormSmoothnessStatement.{u}` and proves
that `E.torusIwahori` is open in `rationalPointTopology K E.T.toGrp.X`. The
hypothesis, applied to `K`, `L`, `E.T` and `E.isSplitTorus`, gives that the
underlying scheme morphism of `GaloisNorm.norm K L E.T` is smooth. The published
`isOpenMap_rationalPoint_of_smooth F henselianSmoothRationalPointOpenMap` then
makes the induced map `R(K) → T(K)` open between the two rational-point
topologies. By `torusIwahori_eq_map_weilKernel`, `E.torusIwahori` is the image of
the open set `weilKernel` under this map.

`isOpen_zeroPoints` assumes both statements and `[IsAffine H.X.left]`, and proves
that `E.zeroPoints` is open in `rationalPointTopology K H.X`. The product
hypothesis, applied to `K`, `H`, `E.D`, `E.C`, `E.T`, `E.d`, `E.π`, `E.i`,
`E.isSimplyConnectedDerivedCover`, and the maximal-torus part of
`E.isMaximallySplitMaximalTorus`, gives that
`(subgroupProductMap (E.π ≫ E.d) E.i).left` is smooth. The same Henselian
open-map theorem makes `p ↦ p ≫ subgroupProductMap (E.π ≫ E.d) E.i` open from
`rationalPointTopology K (E.C.X ⊗ E.T.toGrp.X)` to `rationalPointTopology K H.X`.
The affineness of `(E.C.X ⊗ E.T.toGrp.X).left` comes from the published
`isAffine_coverTorus`. The published `isOpen_zeroPoints_of_isOpenMap` combines
this open map with `isOpen_torusIwahori`.

## Descent to `F`

Let `G` be a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
`P : ParahoricBuildingData G`. `ParahoricBuildingData.isOpen_centralizerZero`
assumes both statements. Its conclusion binds the same local instances as
`CentralizerZeroCompactOpenStatement`: affineness of `G.X.left` from
`isAffine_of_isAffineHom`, affineness of `P.centralizer.Z.X.left` from the
closed immersion `P.centralizer.j`, and `rationalPointTopology F P.centralizer.Z.X`.
Under these instances `P.centralizerZero` is open.

By definition, `P.centralizerZero` is
`anisotropicZeroPoints P.zeroDatum.centralizerDatum`, the preimage of
`P.zeroDatum.centralizerDatum.zeroPoints` under extension of scalars from `F` to
`K`. The proof applies `isOpen_zeroPoints` to `P.zeroDatum.centralizerDatum`,
with affineness of the base-changed centralizer from the published
`isAffine_ambient`. It then applies the published
`isOpen_anisotropicZeroPoints_of_isOpen`, which takes the preimage under the
continuous extension-of-scalars map.

## Scope

- `DerivedCoverTorusProductSmoothStatement.{u}` and
  `GaloisNormSmoothnessStatement.{u}` are hypotheses at the universe `u` of `F`.
  They are not proved here.
- No compactness is proved. The module does not prove
  `CentralizerZeroCompactOpenStatement`.
- Normality and independence of choices, the other parts of KP Lemma 2.6.24,
  are not addressed.
