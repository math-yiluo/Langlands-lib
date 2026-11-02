# Diagonal cocharacters and weight-block subgroups of `GL_n`

This module defines the diagonal cocharacter `λ(t) = diag(t^{e_i})` of the general linear group
scheme `GL_n` over `Spec R`, for a weight vector `e : n → ℤ`. It also defines the subgroup
functors of block upper triangular, block diagonal and block unipotent invertible matrices for the
weight blocks `{i | e i = c}`. These are the explicit groups that the dynamic subgroup functors
`P_{GL_n}(λ)`, `Z_{GL_n}(λ)` and `U_{GL_n}(λ)` are expected to equal. For the decreasing weights
of an ordered block shape `B : Langlands.GeneralLinear.BlockShape N`, the module proves that the
three matrix subgroups are the Library's `B.parabolic`, `B.leviSubgroup` and
`B.unipotentSubgroup` (module `Langlands.Group.GL.Blocks`). It also proves that the block
diagonal projection agrees with `B.leviProjection`, and it builds the corresponding subgroup
functors from those Library subgroups. The comparison with `Langlands.GroupScheme.Dynamic` is
left to later statements.

All declarations are in the namespace `Langlands.GroupScheme.GeneralLinear`. The index type `n` is
any `Type` with `[Fintype n]` and `[DecidableEq n]`, as in the Library module
`Langlands.GroupScheme.GeneralLinear`. The weights `e` are arbitrary integers. They may repeat and
need not be ordered. `GL n A` is Mathlib's `Matrix.GeneralLinearGroup n A`.

## Sources

- Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), §2.1, Example 2.1.1, printed
  pp. 45–47 (PDF pp. 71–73). For `λ(t) = diag(t^{e_1}, …, t^{e_n})` the conjugation formula (2.1.1)
  on p. 46 reads `λ(t) g λ(t)⁻¹ = (t^{e_r − e_s} a_{rs})`. Its `(r, s)` entry has a negative
  exponent of `t` exactly when `e_r < e_s`. So `P_G(λ)` consists of the `g = (a_{rs})` with
  `a_{rs} = 0` whenever `e_r < e_s`. `U_G(λ)` consists of the points of `P_G(λ)` acting trivially
  on the associated graded space, that is, whose diagonal blocks are identity matrices. On p. 47,
  `Z_G(λ) = P_G(λ) ∩ P_G(−λ)` is the block diagonal subgroup `∏ GL(V_{χ_j})`.
- Conrad, *Reductive group schemes* (2014), Example 4.1.8 (p. 114). It concerns `G = SL_n`,
  not `GL_n`, over any ring, for strictly decreasing weights `e_1 > ⋯ > e_n`. There `P_G(λ)` is
  the upper triangular subgroup, `U_G(λ)` the strictly upper triangular (unipotent) subgroup and
  `Z_G(λ)` the diagonal subgroup. For pairwise distinct weights that are not monotone, `P_G(λ)`
  is a conjugate of the upper triangular subgroup by a permutation matrix. This module uses the
  example only as a cross-check of the sign convention. Its source for `GL_n` is CGP
  Example 2.1.1.

CGP lists the basis so that `e_1 ≥ ⋯ ≥ e_n`. This module does not order `n`. Instead, every
condition is stated by comparing the weights `e i` and `e j`, so no ordering of the basis is
needed. For weights listed in decreasing order, "zero whenever `e i < e j`" means block upper
triangular.

## Matrix groups over a commutative ring

Let `A` be a commutative ring.

- `diagonalUnits A e : Aˣ →* GL n A` sends a unit `t` to `diag(t ^ e i)`
  (`coe_diagonalUnits`). It uses integer powers of units, so negative weights are allowed.
  `map_diagonalUnits` gives compatibility with ring homomorphisms.
- `blockParabolicSubgroup A e` consists of the invertible matrices whose `(i, j)` entry vanishes
  whenever `e i < e j` (`mem_blockParabolicSubgroup`). In Lean the carrier is Mathlib's
  `Matrix.BlockTriangular` for the order-reversed weights `OrderDual.toDual ∘ e`. Closure under
  inverses is Mathlib's `Matrix.blockTriangular_inv_of_blockTriangular`.
- `blockLeviSubgroup A e` consists of the invertible matrices whose `(i, j)` entry vanishes
  whenever `e i ≠ e j` (`mem_blockLeviSubgroup`). These are the block diagonal matrices. The
  subgroup laws come from block triangularity for both `e` and its order reversal.
- `blockUnipotentSubgroup A e` consists of the invertible matrices whose `(i, j)` entry equals
  the `(i, j)` entry of the identity matrix whenever `e i ≤ e j` (`mem_blockUnipotentSubgroup`).
  These are the block upper triangular matrices whose diagonal blocks are identity matrices.

Supporting constructions:

- `blockDiagonalPart A e M` keeps the entries `(i, j)` of `M` with `e i = e j` and replaces the
  other entries by `0` (`blockDiagonalPart_apply`, `blockDiagonalPart_one`). By
  `blockDiagonalPart_mul`, it is multiplicative on matrices that are block triangular for the
  order-reversed weights.
- `blockLeviProjection A e` is the resulting homomorphism from `blockParabolicSubgroup A e` to
  `GL n A`. The inverse of the image of `g` is the block diagonal part of `g⁻¹`
  (`coe_blockLeviProjection`). In CGP's terms it sends `g` to the automorphism it induces on the
  associated graded space.
- `blockUnipotent_iff` says that `M` lies in the unipotent carrier exactly when `M` is block
  triangular for the order-reversed weights and its block diagonal part is `1`. The subgroup laws
  of `blockUnipotentSubgroup` are proved from this and from `blockDiagonalPart_mul`.
- `map_mem_blockParabolicSubgroup`, `map_mem_blockLeviSubgroup` and
  `map_mem_blockUnipotentSubgroup` say that `Matrix.GeneralLinearGroup.map f` preserves the three
  subgroups for every ring homomorphism `f : A →+* B`.

## Group-scheme constructions over `Spec R`

Let `R : CommRingCat`, and let `groupScheme n R` be the Library general linear group scheme. Its
`T`-points are identified with `GL n Γ(T, 𝒪_T)` by the Library equivalence `pointsEquiv n R T`.

- `diagonalPoints n R e T` sends a `T`-point of the Library multiplicative group `Gm (Spec R)`,
  that is a unit `t` of `Γ(T, 𝒪_T)` under `Gm.pointsEquiv`, to the point of `GL_n` with matrix
  `diag(t ^ e i)` (`pointsEquiv_diagonalPoints`). `diagonalPoints_naturality` proves naturality in
  `T`, from `map_diagonalUnits` and the naturality of the two Library point equivalences.
- `diagonalCocharacter n R e : (Gm (Spec R)).toGrp ⟶ groupScheme n R` is the homomorphism of group
  schemes built from these points by the Library constructor `homOfPoints`. It is a cocharacter
  in the sense of `Langlands.GroupScheme.Dynamic`. By `pointsEquiv_diagonalCocharacter` its value
  on a point `t` is `diag(t ^ e i)`, the `λ` of CGP Example 2.1.1.
- `ofMatrixSubgroups H hH` takes a family of subgroups `H A ≤ GL n A`, one for each commutative
  ring `A` in the universe of `R`, preserved by every ring homomorphism (`hH`). It gives the
  subgroup functor (see `Langlands.GroupScheme.SubgroupFunctor`) whose `T`-points are the points
  with matrix in `H Γ(T, 𝒪_T)` (`mem_ofMatrixSubgroups`). Restriction along `a : T' ⟶ T` acts on
  matrices by the ring map `Γ(T, 𝒪_T) → Γ(T', 𝒪_{T'})` of `a` (Library `pointsEquiv_naturality`),
  so `hH` gives stability under restriction.
- `blockParabolic n R e`, `blockLevi n R e` and `blockUnipotent n R e` are the subgroup functors of
  `groupScheme n R` given by the three matrix subgroups. Their `T`-points are characterized by
  `mem_blockParabolic` (entries `(i, j)` with `e i < e j` vanish), `mem_blockLevi` (entries with
  `e i ≠ e j` vanish) and `mem_blockUnipotent` (entries with `e i ≤ e j` agree with the identity
  matrix). All tests `T` over `Spec R` are included, not only affine ones.

## Bridge to the Library's ordered block shapes

The Library module `Langlands.Group.GL.Blocks` defines, for `B : BlockShape N` (positive block
sizes `B.size i`, `i : Fin B.length`, with sum `N`), the standard upper block parabolic
`B.parabolic A`, the block diagonal subgroup `B.leviSubgroup A` (the image of
`B.leviEmbedding A`), the block unipotent subgroup `B.unipotentSubgroup A`, and the diagonal-block
projection `B.leviProjection A : B.parabolic A →* B.Levi A`, all inside
`Langlands.GeneralLinear N A = GL (Fin N) A`. A position `a` in block `i` is the standard
coordinate `B.index i a`, through `B.indexEquiv`. The section `BlockShape` of this module
connects these Library groups to the weight-block groups. It does not define them again.

- `blockShapeWeight B : Fin N → ℤ` gives the coordinate `B.index i a` the weight `-i`
  (`blockShapeWeight_index`). The weights decrease along the block order, as in CGP's convention
  `e_1 ≥ ⋯ ≥ e_n`. `blockShapeWeight_lt_iff` and `blockShapeWeight_eq_iff` translate comparisons
  of weights into comparisons of block numbers: weight of block `i` < weight of block `j` exactly
  when `j < i`. `exists_eq_index` and `index_eq_index_iff` say that `B.index` numbers the
  coordinates bijectively.
- `blockParabolicSubgroup_blockShapeWeight`: `blockParabolicSubgroup A (blockShapeWeight B) =
  B.parabolic A`. The condition "entry `(k, l)` vanishes when `e k < e l`" becomes the Library's
  `mem_parabolic_iff`: blocks strictly below the diagonal vanish.
- `blockLeviSubgroup_blockShapeWeight`: `blockLeviSubgroup A (blockShapeWeight B) =
  B.leviSubgroup A`. A matrix with zero entries between distinct blocks is
  `B.leviEmbedding A (B.leviProjection A g)`. The proof checks this entrywise with the Library's
  `leviEmbedding_apply_same` and `leviEmbedding_apply_ne`.
- `blockUnipotentSubgroup_blockShapeWeight`: `blockUnipotentSubgroup A (blockShapeWeight B) =
  B.unipotentSubgroup A`, through the Library's `mem_unipotentSubgroup_iff`: in the parabolic,
  with identity diagonal blocks.
- `leviEmbedding_leviProjection`: for `g` in the weight-block parabolic, `B.leviEmbedding A
  (B.leviProjection A g') = blockLeviProjection A (blockShapeWeight B) g`. Here `g'` is `g`
  viewed in `B.parabolic A` through `MulEquiv.subgroupCongr` of the parabolic equality. So the
  block diagonal part used in this module is the Library's diagonal-block projection followed by
  the block diagonal embedding.
- `blockShapeCocharacter B R` is `diagonalCocharacter (Fin N) R (blockShapeWeight B)`. It acts on
  the `i`-th block by `t ^ (-i)`.
- `blockShapeParabolic B R`, `blockShapeLevi B R` and `blockShapeUnipotent B R` are the subgroup
  functors of `groupScheme (Fin N) R` whose `T`-points are the points with matrix in
  `B.parabolic Γ(T, 𝒪_T)`, `B.leviSubgroup Γ(T, 𝒪_T)` and `B.unipotentSubgroup Γ(T, 𝒪_T)`
  (built with `ofMatrixSubgroups`). Their stability under ring homomorphisms is transported from
  the weight-block lemmas through the equalities above.
- `blockParabolic_blockShapeWeight`, `blockLevi_blockShapeWeight` and
  `blockUnipotent_blockShapeWeight` state the equalities of subgroup functors
  `blockParabolic (Fin N) R (blockShapeWeight B) = blockShapeParabolic B R`, and likewise for the
  Levi and unipotent functors.

The weight-block groups remain, because a diagonal cocharacter need not have its weights in
decreasing order, and equal weights may sit in non-consecutive positions. After a permutation of
the coordinates, such a cocharacter has decreasing weights. Conrad remarks this in Example 4.1.8
for pairwise distinct weights. This module does not prove any such conjugation statement.

## Scope

The module proves no equality between these block subgroup functors (weight-block or block-shape)
and the dynamic subgroup functors `Dynamic.parabolic`, `Dynamic.centralizer` and
`Dynamic.unipotent` of `diagonalCocharacter n R e`. Those equalities are CGP's computation in
Example 2.1.1 and are planned as separate statements. For block shapes, those statements will use
`blockShapeCocharacter`, `blockShapeParabolic`, `blockShapeLevi` and `blockShapeUnipotent`. The
module also proves no representability by closed subschemes, no isomorphism of the block diagonal
subgroup functor with the product of the `GL_{B.size i}`, and no semidirect product
decomposition.
