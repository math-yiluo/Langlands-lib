# Permuted cocharacter bases of induced tori and rational points from equivariant units

This internal helper module, used by the proof of KP Corollary 11.1.9
(`inducedTorusKottwitzRationalSurjectivity`), has two parts. First, it turns
the permuted character basis of an induced torus (KP Definition 2.5.1, the
Library's `IsInducedTorus`) into permuted cocharacter bases, over the splitting
field and over `F^sep`. Second, it constructs rational points from Galois
equivariant families of units. It adds no assertion from the literature; the
constructions are derived from existing Library lattice and point APIs.

All declarations are in `Langlands.Geometry.Building.Kottwitz.InducedCocharacterBasis`.

## Dual bases

`k` and `E` are fields with `Algebra k E`. `T` is a commutative group scheme
over `Spec k` with `hE`, a proof that `T_E` is split. `b` is a `ℤ`-basis, indexed
by a finite `J`, of `characterLattice` of `T_E`.

* `dualBasis T hE b` is the cocharacter basis of `T_E` dual to `b`. It is
  `b.dualBasis` transported by `(cocharacterDualEquiv _ hE).symm`, where the
  equivalence comes from the perfect character–cocharacter pairing of a split
  torus (`Kottwitz.SplitValuation`). `latticePairing_dualBasis` gives
  `⟨b i, dualBasis j⟩ = if i = j then 1 else 0`.
* Assume `hb`: every Galois element sends each `b i` to some `b j`. Then
  `indexHom T b hb : (E ≃ₐ[k] E) →* Equiv.Perm J` is the Library's
  `PermutationBasis.indexAction`. `galoisRepresentation_basis` restates its
  defining property.
* `galoisRepresentation_dualBasis`: the Galois action on cocharacters sends
  `dualBasis j` to `dualBasis (indexHom σ j)`. Proof: compare pairings with every
  `b i`. Use `latticePairing_galoisRepresentation_right` and
  `Equiv.Perm.inv_eq_iff_eq`.

## Geometric bases

Now `F` is a nonarchimedean local field. `E` is a finite Galois intermediate
field of `F^sep/F` over which `T` splits, `T` is affine, and `b`, `hb` are as
above.

* `not_isOfFinOrder_uniformizer`: the image in `Eˣ` of the base uniformizer
  `SplitTorusValuation.uniformizerUnit F` has infinite order. Its field order is
  `1`.
* `isSplit_sepClosure`: `T` splits over `F^sep`
  (`IsSplitTorus.baseChange_fieldTower`).
* `geometricBasis F E T hE b` is the basis of the geometric cocharacters
  `geometricCocharacters F (SeparableClosure F) T` obtained by applying the
  bijective map `extendGeometricCocharacters F E (SeparableClosure F) T` to
  `dualBasis`. `geometricBasis_apply` unfolds it.
* `galoisIndexHom F E T b hb` is the composite of `indexHom` with
  `AlgEquiv.restrictNormalHom E`. It is the action of `Gal(F^sep/F)` on indices
  through `Gal(E/F)`.
* `galoisRepresentation_geometricBasis`: `Gal(F^sep/F)` permutes the geometric
  basis through `galoisIndexHom`. Proof: `extendGeometricCocharacters_galois` with
  `σ.restrictNormal E`, then `galoisRepresentation_dualBasis`.

## Rational points from equivariant units

`exists_rationalPoint`: let `x : J → Eˣ` satisfy
`x (indexHom σ j) = σ (x j)` for every `σ ∈ Gal(E/F)`. Then there is
`t : rationalPoints T.toGrp` whose extension to `E`,
`GaloisPoint.extend F E T.toGrp (rationalCoeffEquiv F T.toGrp t)`, is the point
`coefficientEvaluation F E T (∑ j, x j ⊗ dualBasis j)`, i.e. `∏ⱼ (dualBasis j)(x j)`.

Proof. Call the point `y`. For each `σ`, `coefficientEvaluation_galois_tmul`
computes the conjugate of each pure evaluation. Equivariance of `x` and
`galoisRepresentation_dualBasis` turn the conjugated sum into the same sum,
reindexed by the permutation `indexHom σ` (`Equiv.sum_comp`). So `y` lies in
`GaloisPoint.fixedSubgroup`, and `GaloisPoint.mem_range_extend_iff` (finite
Galois descent of affine points) gives a base point. `rationalCoeffEquiv`
converts it to a rational point.
