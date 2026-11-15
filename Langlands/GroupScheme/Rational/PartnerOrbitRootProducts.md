# Root-group products over partnered orbits of simple roots

Module `Langlands.GroupScheme.Rational.PartnerOrbitRootProducts`, namespace
`Langlands.GroupScheme.SplitPinning`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SU3 half.

## Purpose

Module `PartnerOrbitUnitaryCoordinates` builds unitary root coordinates from
`unitaryRho : SU₃(L/E) →* G(k)`. It assumes abstract hypotheses on the relative root
groups: membership (`hmem`, `hmem2`), product decomposition (`hprod`, `hprod2`) and
uniqueness (`huniq`), all stated with products of pair families `D.pairOrbitSL3`. This
module derives those hypotheses from one assumption: each relative root group is the ordered
product, with unique factors, of the absolute root groups of the pieces. That assumption
has exactly the form of the conclusion of the published
`Geometry.Building.SplitRelativeRootGroupProductStatement`, so a later module can feed it in
directly. The module also proves two facts about `unitaryRho` used for the coroot and Weyl
clauses. The diagonal torus element goes to a product of simple-coroot points
(`rationalExtend_unitaryRho_diagonal`). The antidiagonal Weyl element goes into the
normalizer of the torus (`unitaryRho_weylElement_mem`).

The mathematics is the standard description of the root groups of a quasi-split group over a
splitting field. Inside the `A₂` subgroup of an adjacent pair `r, π r` of simple roots, the
roots `π r`, `r + π r`, `r` give the three entries of an upper unitriangular `3 × 3` matrix.
The root group of `r + π r` is the conjugate of that of `π r` by the Weyl element of `r`.
See Borel–Tits, *Groupes réductifs*, §4, and Kaletha–Prasad, *Bruhat–Tits theory*,
Prop. 7.1.1 and its proof. The Lean development is internal, and every step is proved here
or taken from the Library.

Notation: `SL₃(K)` is `Matrix.SpecialLinearGroup (Fin 3) K`; `left`, `right` are the `SL₂`
blocks of `TernaryPresentation` (indices `{0,1}` and `{1,2}`); `w` is
`BinaryUpper.weylMatrix = [[0,-1],[1,0]]`; `upper t`, `lower t`, `diag u` are the `SL₂`
matrices of `BinaryPresentation`. `U_χ` is `Geometry.Building.rootGroupPoints p.inclusion χ`.

## Matrices (section `Matrices`, any field `K`)

- `cornerUpper t = 1 + t E₀₂` and `cornerLower t = 1 + t E₂₀` (defs), with `coe_cornerUpper`
  and `coe_cornerLower`.
- `left_weyl_mul_cornerUpper`: `left w * cornerUpper t = right (upper t) * left w`;
  `left_weyl_mul_cornerLower`: `left w * cornerLower t = right (lower t) * left w`.
- `coe_upperTriple`: `right (upper u) * cornerUpper w * left (upper v)` is the matrix
  `[[1, v, w], [0, 1, u], [0, 0, 1]]`. `coe_lowerTriple`:
  `left (lower v) * cornerLower w * right (lower u)` is `[[1, 0, 0], [v, 1, 0], [w, u, 1]]`.
- `eq_upperTriple`: an upper unipotent `g` (`IsUpperSL3 g`) equals
  `right (upper g₁₂) * cornerUpper g₀₂ * left (upper g₀₁)`. `eq_lowerTriple`: a lower
  unipotent `g` equals `left (lower g₁₀) * cornerLower g₂₀ * right (lower g₂₁)`.
  `isUpperSL3_upperTriple` and `isLowerSL3_lowerTriple` give the converse.
- `isCentralUpperSL3_cornerUpper`, `isCentralLowerSL3_cornerLower`, `eq_cornerUpper`,
  `eq_cornerLower`: the central upper (lower) unipotent matrices are exactly the corner
  transvections.
- `cornerUpper_mul_neg`, `cornerLower_mul_neg`: inverses of corner transvections.
  `outer_cornerUpper`, `outer_cornerLower`: the outer involution sends the corner
  transvection with parameter `t` to the one with parameter `-t`.
- `isUpperSL3_outer`, `isLowerSL3_outer`, `isCentralUpperSL3_outer`,
  `isCentralLowerSL3_outer`: the outer involution preserves these four classes.
- `gramSL3` (def): the antidiagonal matrix `J = SU3Root.gram K` in `SL₃(K)`.
  `gramSL3_eq`: `J = left w * right w * left w`. `map_gramSL3`: ring maps fix `J`.
- `coe_left_diag_mul_right_diag`: `left (diag s) * right (diag t)` is
  `diag(s, s⁻¹ t, t⁻¹)`.

## A pair of adjacent simple roots (section `Split`)

Here `p` is a split pinning of `G` over a field `k`, `x` a family of normalized simple root
parametrizations and `hAdj` the published `AdjacentSimpleRootSpecialLinearStatement`. For
simple roots `a, b` with both pairings `-1`, `pairSL3 hAdj x a b` is the ternary
homomorphism of module `PartnerOrbitSpecialUnitary`.

- `weylInvPoint x a` (def): the inverse of `rootSL2 x a w`, as a point of
  `normalizerPoints p.inclusion`; `coe_weylInvPoint`.
- `weylAction_weylInvPoint`: it acts on characters by the reflection
  `χ ↦ χ - ⟨χ, a^∨⟩ a`. The proof writes `(rootSL2 x a w)⁻¹` as the opposite-pair product
  `x₋(-1) x₊(1) x₋(-1)` and applies the Library lemma
  `Geometry.Building.weylAction_oppositeFactorPair_eq`. It needs
  `[LocallyOfFiniteType G.X.hom]`. Consequences: `weylAction_weylInvPoint_root`
  (`b ↦ a + b`) and `weylAction_weylInvPoint_neg_root` (`-b ↦ -(a + b)`) when
  `⟨b, a^∨⟩ = -1`.
- `conj_mem_rootGroupPoints_iff`: for a normalizer point `n`,
  `n g n⁻¹ ∈ U_{n·χ} ↔ g ∈ U_χ`. This is the Library `RelativeRoot.normalizer_conj_mem_iff`
  on the base test.
- `pairSL3_left_upper`, `pairSL3_right_upper`, `pairSL3_left_lower`, `pairSL3_right_lower`:
  the images of the block transvections are the root points `x₊`, `x₋` of `a` and `b`.
- `pairSL3_cornerUpper`, `pairSL3_cornerLower`: the corner transvections go to the
  conjugates by `weylInvPoint x a` of the root points `x₊(t)`, `x₋(t)` of `b`.
- `pairSL3_cornerUpper_mem`, `pairSL3_cornerLower_mem`: these lie in `U_{a+b}` and
  `U_{-(a+b)}`. `exists_pairSL3_cornerUpper_eq`, `exists_pairSL3_cornerLower_eq`: every
  point of these root groups is such an image. `pairSL3_cornerUpper_injective`,
  `pairSL3_cornerLower_injective`: the parameter is unique.
- `pairSL3_gramSL3_mem`: `pairSL3 a b J` normalizes the pinned torus, by `gramSL3_eq` and
  the Library `rootSL2_weylMatrix_mem`.
- `pairSL3_left_diag_mul_right_diag`: `left (diag s) * right (diag t)` goes to the image
  under `p.inclusion` of `a^∨(s) b^∨(t)` (`p.simpleCorootPoint`).

## Partnered orbits (namespace `PartnerData`)

`D : PartnerData O` is a partner structure on a set `O` of simple roots (module
`PartnerOrbitSpecialUnitary`), `D.orientation` its chosen half, and
`e : D.orientation ≃ Fin n` an enumeration. Write `r_l` for the member `e.symm l` of the
orientation.

- `pairOrbitSL3_eq_prod_ofFn`: `D.pairOrbitSL3 hAdj x h` is the ordered product, along `e`,
  of `pairSL3 r_l (π r_l) (h r_l)`.
- `pairExtend M` (def): the family equal to `M` on the orientation and to
  `outer (M (π a))` off it. `pairExtend_of_mem`, `pairExtend_of_not_mem`,
  `isPairFamily_pairExtend` (it is a pair family), `pairOrbitSL3_pairExtend` (same product
  as `M`), `pairExtend_prop` (a property preserved by `outer` and true on the orientation
  holds on `O`).
- `eq_of_eq_on_orientation`: two pair families agreeing on the orientation agree on `O`.

### Upper pieces (section `UpperPieces`)

- `upperPieceRoot e l c` (def): the roots `π r_l`, `r_l + π r_l`, `r_l` for `c = 0, 1, 2`.
  `upperPieceEnum e` (def): the same along `Fin (n * 3)` through `finProdFinEquiv`;
  `upperPieceEnum_finProd`.
- `upperPiecePoint u w v l c` (def): the three factors
  `pairSL3 r_l (π r_l)` of `right (upper (u l))`, `cornerUpper (w l)`,
  `left (upper (v l))`. `upperPiecePoint_mem`: they lie in `U_{upperPieceRoot e l c}`.
  `prod_upperPiecePoint`: their ordered product is the product over `l` of the images of
  the triples. It uses the Library `Geometry.Building.list_ofFn_prod_finProd`.
- `pairOrbitSL3_eq_prod_upperPiecePoint`: for a family `h` that is upper unipotent on `O`,
  `D.pairOrbitSL3 hAdj x h` is the ordered product of the factors with the entries of `h`.

Let `U` be a subgroup of `G(k)` with
`hU : g ∈ U ↔ ∃ y : (k' : Fin (n * 3)) → U_{upperPieceEnum e k'}, g = ∏ y k'` (ordered
product), and, for uniqueness, `hU'`: the factors of such an ordered product are unique.

- `pairOrbitSL3_mem_of_isUpper` (from `hU`): products of families that are upper unipotent
  on `O` lie in `U`.
- `exists_isUpper_pairOrbitSL3_eq` (from `hU`): every `g ∈ U` is the product of a pair family
  that is upper unipotent on `O`. The proof writes each factor through
  `RootParametrization.exists_rationalPoint_eq` or `exists_pairSL3_cornerUpper_eq`, then
  uses `pairExtend`.
- `eq_of_isUpper_pairOrbitSL3_eq` (from `hU'`): two such pair families with the same product
  agree on `O`.

### Lower pieces (section `LowerPieces`)

The same for the negative roots, with the pieces ordered `-r_l`, `-(r_l + π r_l)`,
`-π r_l` and the factors `left (lower (v l))`, `cornerLower (w l)`, `right (lower (u l))`:
`lowerPieceRoot`, `lowerPieceEnum` (defs), `lowerPieceEnum_finProd`, `lowerPiecePoint`
(def), `lowerPiecePoint_mem`, `prod_lowerPiecePoint`,
`pairOrbitSL3_eq_prod_lowerPiecePoint`, `pairOrbitSL3_mem_of_isLower`,
`exists_isLower_pairOrbitSL3_eq`, `eq_of_isLower_pairOrbitSL3_eq`.

### Doubled roots (section `DoublePieces`)

- `doubleRoot e l` (def): `r_l + π r_l`.
- For a subgroup `U` with `g ∈ U ↔ ∃ y : (l : Fin n) → U_{doubleRoot e l}, g = ∏ y l`:
  `pairOrbitSL3_mem_of_isCentralUpper` and `exists_isCentralUpper_pairOrbitSL3_eq` (the
  central upper families, the analogues of the two statements above).
- With `-doubleRoot e l`: `pairOrbitSL3_mem_of_isCentralLower` and
  `exists_isCentralLower_pairOrbitSL3_eq`.

### Torus and Weyl element (section `TorusWeyl`)

- `pairOrbitSL3_gramSL3_mem`: the product of the constant family `J` normalizes the pinned
  torus.
- `prod_eq_prod_orientation`: for `[Fintype O]` and a commutative monoid, the product over
  `O` equals the product over the orientation of `f r * f (π r)`.
- `pairOrbitSL3_diag`: the product of the family `left (diag (t a)) * right (diag (t (π a)))`
  is the image under `p.inclusion` of `∏ b : O, b^∨(t b)`.

## Descended homomorphism (section `Galois`)

The setting is that of `PartnerOrbitSpecialUnitary` and `PartnerOrbitUnitaryCoordinates`:
a finite Galois extension `K / k`, the pinning `p` of `G_K` with Galois-compatible data, a
Galois-stable partnered set `O`, embeddings `τ a : L →ₐ[k] K` with `τ (π a) = τ a ∘ c̄`, and
`unitaryRho : SU₃(L/E) →* G(k)` for the ring involution `c` of `L`.

- `unitaryRho_weylElement_mem` (for `[Mono i.hom.hom.left]`): the image of
  `SU3Root.weylElement` lies in `normalizerPoints i`. After scalar extension it is the
  product of the constant family `J` (`map_gramSL3`), which normalizes the pinned torus
  (`pairOrbitSL3_gramSL3_mem`). The Library `mem_normalizerPoints_rationalExtend_iff` and
  `mem_normalizerPoints_baseChange_of_pinning` (module `OrthogonalOrbitWeylNormalizer`)
  descend this to `i`.
- `rationalExtend_unitaryRho_diagonal` (for `[Fintype O]`): the scalar extension of the
  image of `SU3Root.diagonal c t = diag(t, t̄/t, 1/t̄)` is the image under `p.inclusion` of
  `∏ b : O, b^∨(τ_b t)`. Under `τ a` the diagonal matrix becomes
  `left (diag (τ_a t)) * right (diag (τ_{π a} t))`, because `τ_a (t̄) = τ_{π a} t`. Then
  `pairOrbitSL3_diag` applies.
