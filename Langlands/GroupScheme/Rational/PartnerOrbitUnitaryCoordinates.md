# Unitary coordinates on relative root groups from partnered orbits of simple roots

Module `Langlands.GroupScheme.Rational.PartnerOrbitUnitaryCoordinates`, namespace
`Langlands.GroupScheme.SplitPinning`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SU3 half.

## Purpose

Module `PartnerOrbitSpecialUnitary` builds `unitaryRho : SU₃(L/E) →* G(k)` from a set `O` of
simple roots that falls into `A₂` pairs. This module computes this homomorphism on the
upper and lower unipotent root parameters `SU3Root.Parameters c`. It proves:

1. torus conjugation multiplies the parameters by a scalar (`conj_unitaryRho_upper/lower`);
2. under abstract hypotheses on the relative root group of `b` (membership, product
   decomposition, uniqueness, and descent of scalar families), the upper parameters give a
   group isomorphism onto the rational root group of `b`, and the lower parameters one onto
   that of `-b` (`upperUnitaryEquiv`, `lowerUnitaryEquiv`);
3. under the analogous hypotheses for `2 • b`, the root group of `2 • b` is the image of the
   central parameters (`mem_double_iff_upper/lower`).

These are the `positive`, `negative`, `double` and `conjugation` clauses of
`Geometry.Building.RootUnitaryCoordinatesOn`. A later module supplies the abstract
hypotheses for the simple-root fiber of a multipliable relative root. The construction is
the standard one for quasi-split `SU₃` root groups (Borel–Tits, *Groupes réductifs* §4;
Kaletha–Prasad, *Bruhat–Tits theory*, Prop. 7.1.1 and its proof). The Lean development is
internal and every step is proved here or taken from the Library.

## Matrices (section `Matrices`)

For a field `K` and units `l, m`:

- `diagConjLeft l m = (lm, m, 1)` and `diagConjRight l m = ((lm)⁻¹, m⁻¹, 1)` (defs), with
  `diagonal_diagConjLeft_mul_right` and `diagonal_diagConjRight_mul_left` (the two
  diagonal matrices are mutually inverse).
- `diagConj l m : SL₃(K) →* SL₃(K)` (def): conjugation by `diag(lm, m, 1)`.
  `diagConj_apply` gives its entries.
- `diagConj_left_upper`, `diagConj_left_lower`, `diagConj_right_upper`,
  `diagConj_right_lower`: on the two `SL₂` blocks `TernaryPresentation.left/right`, it
  multiplies the upper coordinate of the left block by `l`, the lower one by `l⁻¹`, and the
  upper and lower coordinates of the right block by `m` and `m⁻¹`.

## Root parameters (section `Parameters`)

For a commutative ring `A` with ring involution `c`:

- `upperSL3 q` (def): the matrix `[[1, q₁, q₂], [0, 1, c̄ q₁], [0, 0, 1]]` of
  `SU3Root.Parameters.matrix q`, as an element of `SL₃(A)`; `coe_upperSL3`.
- `lowerSL3 q` (def): the matrix of `SU3Root.oppositeEmbedding c q`, that is
  `[[1, 0, 0], [-c̄ q₁, 1, 0], [q₂, -q₁, 1]]`; `coe_lowerSL3`.
- `upperSL3_mem_twistFixedSubgroup`, `lowerSL3_mem_twistFixedSubgroup`: both are fixed by
  the unitary twist.
- `fixedSpecialUnitaryEquiv_symm_embedding`, `fixedSpecialUnitaryEquiv_symm_opposite`:
  under `SU3Root.fixedSpecialUnitaryEquiv`, the unitary matrices
  `Parameters.embedding c q` and `oppositeEmbedding c q` correspond to `upperSL3 q` and
  `lowerSL3 q` (both `rfl`).
- `IsUpperSL3 g`: `g` is upper unipotent. `IsLowerSL3 g`: its transpose is upper unipotent.
  `isUpperUnipotent_map_iff`, `isUpperSL3_map_iff`, `isLowerSL3_map_iff`: these conditions
  are preserved and reflected by injective ring maps. `isUpperSL3_upperSL3`,
  `isLowerSL3_lowerSL3`.
- `exists_upperSL3_eq`: an upper unipotent twist-fixed matrix is `upperSL3 q` for some `q`
  (Library `SU3Root.Parameters.mem_range_embedding`).
- `isUpperUnipotent_gram_mul_mul_gram`: conjugating a lower unipotent matrix by the
  antidiagonal Gram matrix gives an upper unipotent one.
- `exists_lowerSL3_eq`: a lower unipotent twist-fixed matrix is `lowerSL3 q`. Conjugate by
  `SU3Root.weylElement`, apply `mem_range_embedding`, and conjugate back
  (`weylElement_mul_self`).
- `upperSL3_injective`, `lowerSL3_injective`: read off the entries `(0,1), (0,2)`, resp.
  `(2,1), (2,0)`.
- `IsCentralUpperSL3 g`: upper unipotent with entries `(0,1)` and `(1,2)` zero.
  `IsCentralLowerSL3 g`: lower unipotent with entries `(1,0)` and `(2,1)` zero.
  `isCentralUpperSL3_map_iff`, `isCentralLowerSL3_map_iff` (injective ring maps);
  `isCentralUpperSL3_upperSL3_iff`, `isCentralLowerSL3_lowerSL3_iff`: `upperSL3 q`, resp.
  `lowerSL3 q`, is central iff `q ∈ SU3Root.Parameters.central c`.
- `upperUnitary c`, `lowerUnitary c : Parameters c →* specialUnitarySubgroup c` (defs): the
  Library maps `Parameters.embedding c` and `oppositeEmbedding c` with codomain restricted.
  `fixedSpecialUnitaryEquiv_symm_upperUnitary/lowerUnitary` (both `rfl`).

## Scaling (section `ParameterScaling`)

For a ring map `f : L →+* K` into a field, parameters `q`, a scalar `y : L` and units
`l, m` of `K`:

- `diagConj_map_upperSL3`: if `l = f y` and `m = f (c̄ y)`, then `diagConj l m` sends the
  image of `upperSL3 q` to the image of `upperSL3 (Parameters.scale y q)`.
- `diagConj_map_lowerSL3`: if `l⁻¹ = f (c̄ y)` and `m⁻¹ = f y`, the same holds for
  `lowerSL3`.

`specialLinearMap_injective`: an injective ring map gives an injective map on `SL₃`.

## Torus action (section `Split`)

Variables as in the split part of `PartnerOrbitSpecialUnitary`: a split pinning `p` of `G`
over `k`, normalized simple-root parametrizations `x`, and
`hAdj : AdjacentSimpleRootSpecialLinearStatement`.

- `rootValue w a : kˣ` (def): the value at the torus point `w` of the rational character
  of the simple root `a`. `rationalCharacterEval_neg_root`: the character of `-a` gives
  `(rootValue w a)⁻¹`.
- `conj_rootSL2_upper`, `conj_rootSL2_lower`: conjugation by the image of `w` multiplies
  the upper, resp. lower, coordinate of `rootSL2 x a` by `rootValue w a`, resp. its inverse
  (`LinkedRootParametrization.conj_xpPoint/conj_xmPoint`).
- `conj_pairSL3`: for an `A₂` pair `(a, b)`, conjugation by the image of `w` turns
  `pairSL3 hAdj x a b g` into `pairSL3 hAdj x a b (diagConj (rootValue w a) (rootValue w b) g)`.
  Both sides are homomorphisms of `SL₃(k)`; compare them on the two blocks with
  `TernaryPresentation.hom_ext` and `BinaryPresentation.hom_ext`.
- `PartnerData.conj_pairOrbitSL3`: the same for the pair-orbit product, factor by factor,
  with `diagConj (rootValue w a) (rootValue w (partner a))` at `a`.

## Galois setting (section `Galois`)

Variables as in the Galois part of `PartnerOrbitSpecialUnitary`: `K/k`, a commutative group
scheme `T` with `i : T → G`, a split pinning `p` of `G_K` whose torus is identified with
`T_K` by `eT` (`hT`), Galois compatible simple-root maps (`hx`, `hroot`, `hρpair`, with
`ρ` the Galois action on simple roots), partner data `D` on `O`, with `O` Galois stable
(`hOs`) and the partner map Galois equivariant (`hπρ`).

### Transport (section `Transport`)

- `galoisPair σ h` (def): the family `a ↦ σ(h (ρ σ⁻¹ a))`. `galoisPair_apply`:
  `galoisPair σ h (ρ σ a) = σ(h a)`.
- `isPairFamily_galoisPair`: it preserves pair families (`TernaryPresentation.map_outer`).
- `rationalConjugate_pairOrbitSL3`: for a pair family `h`, Galois conjugation of the product
  of `h` is the product of `galoisPair σ h`. The proof is that of
  `pairOrbitSL3_rationalConjugate` in `PartnerOrbitSpecialUnitary`: conjugate factor by
  factor (`pairSL3_rationalConjugate`) and reindex the orientation by the permutation
  induced by `σ` (`normalize_action_injective`, `noncommProd_univ_equiv`).
- `map_eq_of_rationalExtend_eq`: let `P` be a Galois stable condition on `SL₃(K)` such that
  pair families satisfying `P` on `O` are determined on `O` by their products (`huniq`). If
  the scalar extension of a rational point is the product of such a family `h`, then
  `h (ρ σ a) = σ(h a)` for `a ∈ O`. Indeed `h` and `galoisPair σ h` have the same product,
  by the previous lemma and since rational points are Galois fixed
  (`rationalConjugate_rationalExtend`).

### Fields (section `Field`)

Further variables: a field `L` over `k` with embeddings `τ a : L →ₐ[k] K`, Galois
equivariant on `O` (`hτ`), a ring involution `c` of `L`, and `hτc`:
`τ (partner a) y = τ a (c̄ y)` for `a ∈ O`.

- `map_map_bar`: `τ a ∘ c̄ = τ (partner a)` on `SL₃(L)`, for `a ∈ O`.
- `isPairFamily_map`: for a twist-fixed `g ∈ SL₃(L)`, the family `a ↦ τ a (g)` is a pair
  family (`outer_eq_map_of_mem_twistFixedSubgroup`).
- `exists_twistFixed_map_eq`: assume `hfam`: every family `e : simple roots → K` with
  `e (ρ σ a) = σ (e a)` on `O` is of the form `a ↦ τ a t` on `O` for some `t : L`. Then a
  Galois equivariant pair family `h` comes from a twist-fixed `g ∈ SL₃(L)`:
  `τ a (g) = h a` for `a ∈ O`. Apply `hfam` entrywise. The determinant is `1` because it is
  so after the injective map `τ a₀`. The twist of `g` is `outer (c̄ g)`
  (`unitaryTwist_eq_outer_map`); after `τ a₀` it becomes
  `outer (h (partner a₀)) = h a₀ = τ a₀ (g)`.
- `exists_twistFixed_of_rationalExtend`: the combination of `map_eq_of_rationalExtend_eq`
  and `exists_twistFixed_map_eq`.

From here on `K/k` is finite Galois, and `URho` is local notation for `unitaryRho` with all
the variables.

- `rationalExtend_unitaryRho_upper`, `rationalExtend_unitaryRho_lower`: the scalar
  extension of `URho (upperUnitary c q)` is the product of the family
  `a ↦ τ a (upperSL3 q)`, and likewise for `lower`. Both are instances of
  `rationalExtend_unitaryRho`.
- `conj_unitaryRho_upper`: let `χ : T(k) → L` satisfy
  `τ a (χ z) = rootValue (z_K) a` for `a ∈ O` (with `z_K` the scalar extension of `z`
  transported to the pinned torus by `eT⁻¹`). Then conjugation by `i(z)` sends
  `URho (upperUnitary c q)` to `URho (upperUnitary c (scale (χ z) q))`. Compare scalar
  extensions (`rationalExtend_injective_of_isAffineHom`), use `map_baseChange_map` and
  `hT` to move `i(z)` to the pinned torus, then `PartnerData.conj_pairOrbitSL3` and
  `diagConj_map_upperSL3`; the value at `partner a` is `τ a (c̄ (χ z))` by `hτc`.
- `conj_unitaryRho_lower`: the same for the lower parameters, assuming instead
  `τ a (χ z) = (rootValue (z_K) (partner a))⁻¹` for `a ∈ O`.

### Root groups (sections `Upper` and `Lower`)

Further variables: `G` smooth, a split commutative group scheme `S` (`hS`) with
`iS : S → G`, and a character `bS ≠ 0` of `S`. `UK[b]` denotes the root-group points
`Geometry.Building.rootGroupPoints` of `(iS)_K` at the base change of `b`.

The section `Upper` assumes:

- `hmem`: products of families that are upper unipotent on `O` lie in `UK[bS]`;
- `hprod`: every point of `UK[bS]` is the product of a pair family that is upper unipotent
  on `O`;
- `huniq`: two such pair families with the same product agree on `O`;
- `hfam`, as above, and a member `a₀ ∈ O`.

Results:

- `unitaryRho_upper_mem`: `URho (upperUnitary c q)` lies in the rational root group of
  `bS`. Membership is tested after scalar extension
  (`Geometry.Building.rationalExtend_mem_rootGroupPoints_iff`), where it is `hmem`.
- `unitaryRho_upper_injective`: by `huniq` the families `τ a (upperSL3 q)` and
  `τ a (upperSL3 q')` agree at `a₀`; conclude by injectivity of `τ a₀` and of `upperSL3`.
- `exists_unitaryRho_upper_eq`: every rational point `g` of the root group of `bS` is
  `URho (upperUnitary c q)`. By `hprod`, the scalar extension of `g` is the product of an
  upper unipotent pair family. By `exists_twistFixed_of_rationalExtend` (with
  `P = IsUpperSL3`) the family comes from a twist-fixed matrix `M` over `L`, which is upper
  unipotent, hence `M = upperSL3 q` (`exists_upperSL3_eq`). Compare scalar extensions.
- `upperUnitaryHom` (def) and `upperUnitaryEquiv` (def):
  `SU3Root.Parameters c ≃* rootGroupPoints iS bS`, `MulEquiv.ofBijective` of the two
  previous results. `upperUnitaryEquiv_apply` (`rfl`): its value is
  `URho (upperUnitary c q)`.
- `mem_double_iff_upper`: assume also `2 • bS ≠ 0` and the analogues `hmem2`, `hprod2` of
  `hmem`, `hprod` for `UK[2 • bS]` and central upper families. Then a rational point lies
  in the root group of `2 • bS` iff it is `URho (upperUnitary c q)` for some central `q`.
  The proof is that of `exists_unitaryRho_upper_eq` with `P = IsCentralUpperSL3`; uniqueness
  comes from `huniq`.

The section `Lower` is the same with `-bS`, `IsLowerSL3`, `lowerSL3`, `lowerUnitary` and
`IsCentralLowerSL3`: `unitaryRho_lower_mem`, `unitaryRho_lower_injective`,
`exists_unitaryRho_lower_eq`, `lowerUnitaryHom`, `lowerUnitaryEquiv`,
`lowerUnitaryEquiv_apply`, and `mem_double_iff_lower` (for `2 • -bS`).

## Provenance

Internal construction. The matrices and their characterizations restate results of the
Library modules `Examples/SU3RootParametersMatrix`, `Examples/SU3RootReflection` and
`Examples/SU3MatrixFixedPoints` in `SL₃` form. The Galois descent is the usual entrywise descent along the embeddings
`τ a : L → K`. The abstract hypotheses `hmem`, `hprod`, `huniq`, `hfam` are not proved here.
