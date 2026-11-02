# Dynamic subgroups of `GL_n` for diagonal cocharacters: statements

This module states the computation of the dynamic subgroup functors of the general linear group
scheme for a diagonal cocharacter. The functors are `Dynamic.parabolic`, `Dynamic.centralizer` and
`Dynamic.unipotent` from `Langlands.GroupScheme.Dynamic`. It also states the limit map at `t = 0`
and the decomposition of `P(λ)` into `U(λ)` and `Z(λ)`. The module proves none of the five
statements. A sixth declaration, `DynamicStatement`, is their conjunction. All six
declarations are `Prop`-valued definitions in the namespace `Langlands.GroupScheme.GeneralLinear`,
with one universe parameter `u` for the base ring.

## `DiagonalCocharacterDynamicStatement`

The statement quantifies over every finite index type `n : Type` with decidable equality, every
`R : CommRingCat.{u}` and every weight vector `e : n → ℤ`. For each of them it asserts three
equalities of subgroup functors of `groupScheme n R`, the Library general linear group scheme
over `Spec R`. Here `λ = diagonalCocharacter n R e` is the cocharacter `t ↦ diag(t ^ e i)`.

- `Dynamic.parabolic λ = blockParabolic n R e`: a point `g` over any scheme `T` over `Spec R`
  has an orbit map `t ↦ λ(t) g λ(t)⁻¹` that extends from `T ×_S 𝔾_m` to `T ×_S 𝔸¹` exactly when
  the `(i, j)` entry of `g` is zero whenever `e i < e j`.
- `Dynamic.centralizer λ = blockLevi n R e`: the orbit map is constant exactly when the
  `(i, j)` entry is zero whenever `e i ≠ e j`.
- `Dynamic.unipotent λ = blockUnipotent n R e`: the orbit map extends with value `1` at `t = 0`
  exactly when the `(i, j)` entry equals that of the identity matrix whenever `e i ≤ e j`.

All test schemes `T` over `Spec R` are included, not only affine ones. The weights are arbitrary
integers and need not be ordered or distinct.

## `BlockShapeDynamicStatement`

This version is for an ordered block shape `B : Langlands.GeneralLinear.BlockShape N` (module
`Langlands.Group.GL.Blocks`) and every `R : CommRingCat.{u}`. Here
`λ_B = blockShapeCocharacter B R` acts on the `i`-th block by `t ^ (-i)`. The statement asserts
`Dynamic.parabolic λ_B = blockShapeParabolic B R`, `Dynamic.centralizer λ_B = blockShapeLevi B R`
and `Dynamic.unipotent λ_B = blockShapeUnipotent B R`. The right-hand sides are the subgroup
functors whose points over `T` have matrices in the Library's `B.parabolic`, `B.leviSubgroup`
and `B.unipotentSubgroup` over `Γ(T, 𝒪_T)`. In standard coordinates these are the upper block
triangular, block diagonal and block unipotent matrices.

The module `Langlands.GroupScheme.Dynamic.GeneralLinear` proves that the block-shape functors
equal the weight-block functors for the weights `blockShapeWeight B`
(`blockParabolic_blockShapeWeight` and its two companions). So the second statement is the
first one for these weights, rewritten with the Library's block subgroups.

## `DiagonalCocharacterLimitStatement`

The statement has the same quantifiers `n`, `R` and `e` as `DiagonalCocharacterDynamicStatement`,
and adds every scheme `T` over `Spec R` and every two points `g l : T ⟶ (groupScheme n R).X`.
`Dynamic.HasLimit λ g l` says that the orbit map `t ↦ λ(t) g λ(t)⁻¹` on `T ×_S 𝔾_m` extends to
`T ×_S 𝔸¹` with value `l` at `t = 0`. The statement asserts that this holds if and only if two
conditions hold:

- `g` lies in `blockParabolic n R e` over `T`;
- `pointsEquiv n R T l` is the block diagonal part `blockLeviProjection Γ(T.left, ⊤) e` of the
  block upper triangular matrix `pointsEquiv n R T g`.

Here `pointsEquiv n R T` is the Library isomorphism of the points of `GL_n` over `T` with
`GL n Γ(T, 𝒪_T)`. The matrix `blockLeviProjection` keeps the entries `(i, j)` with `e i = e j`
and sets the others to zero. In particular the limit exists only on `P(λ)`, it is unique, and it
lies in the block diagonal subgroup.

## `DiagonalCocharacterLeviDecompositionStatement`

The quantifiers are `n`, `R`, `e` and every scheme `T` over `Spec R`. Inside the group of points
of `Dynamic.parabolic λ` over `T`, write `U` and `Z` for the points of `Dynamic.unipotent λ` and
`Dynamic.centralizer λ`, as Mathlib subgroups (`Subgroup.subgroupOf`). The statement asserts:

- `U` is a normal subgroup (`Subgroup.Normal`);
- `U` and `Z` are complements (`Subgroup.IsComplement'`): every point of `P(λ)` over `T` is
  uniquely a product `u * z` with `u` in `U` and `z` in `Z`.

With Mathlib's `SemidirectProduct.mulEquivSubgroup`, these two facts give an isomorphism
`U ⋊ Z ≃* P(λ)(T)`, the conjugation action of `Z` on `U` being the twisting. The statement does
not construct that isomorphism and does not state a decomposition of group schemes.

## `BlockShapeLimitStatement`

For an ordered block shape `B`, every `R`, every scheme `T` over `Spec R` and every two points
`g l` of `groupScheme (Fin N) R` over `T`, the statement asserts the following.
`Dynamic.HasLimit (blockShapeCocharacter B R) g l` holds if and only if two conditions hold:

- the matrix `pointsEquiv (Fin N) R T g` lies in `B.parabolic Γ(T.left, ⊤)`;
- `pointsEquiv (Fin N) R T l` equals `B.leviEmbedding` applied to `B.leviProjection` of that
  matrix.

This is the limit statement for the weights `blockShapeWeight B`, rewritten with the Library's
Levi projection and embedding from `Langlands.Group.GL.Blocks`.

## `DynamicStatement`

`DynamicStatement` is the conjunction, in this order and in the same universe `u`, of
`DiagonalCocharacterDynamicStatement`, `BlockShapeDynamicStatement`,
`DiagonalCocharacterLimitStatement`, `DiagonalCocharacterLeviDecompositionStatement` and
`BlockShapeLimitStatement`. It is the single target for a proof of all five.

## Sources

- Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), §2.1, Example 2.1.1, printed
  pp. 45–47 (PDF pp. 71–73). There `k` is any ring and `G = GL(V)` for a finitely generated
  projective `k`-module `V`; the points are taken over every `k`-algebra. Locally on `Spec k`,
  `V` is free with a basis of weight vectors, and `λ(t) = diag(t^{e_1}, …, t^{e_n})`. By formula
  (2.1.1), conjugation multiplies the `(r, s)` entry by `t^{e_r − e_s}`. `P_G(λ)` consists of
  the matrices with `a_{rs} = 0` whenever `e_r < e_s`. `U_G(λ)` is the subgroup acting trivially
  on the associated graded space, that is, with identity diagonal blocks. `Z_G(λ)` is the block
  diagonal subgroup `∏ GL(V_{χ_j})`, and multiplication `Z_G(λ) ⋉ U_G(λ) → P_G(λ)` is an
  isomorphism. The statements here are the special case of a finite free module `R^n` with a
  given diagonal weight vector, so no localization on `Spec R` is needed. CGP test on
  `k`-algebras; the statements here test on all schemes `T` over `Spec R`. The extension
  condition is local on `T`, and Conrad's relative formulation (next item) defines the limit
  on arbitrary test schemes.
- Conrad, *Reductive group schemes* (2014), Theorem 4.1.7 and the remark after Example 4.1.9
  (pp. 112–114): the dynamic construction makes sense over any ring and any base scheme, and
  commutes with base change. Example 4.1.8 there gives the same description for `SL_n` with
  strictly decreasing weights.
- Conrad–Gabber–Prasad, Lemma 2.1.5, printed pp. 50–51 (PDF pp. 76–77), with its proof. For an
  affine group `G` over a ring `k` and a cocharacter `λ`, the map `P_G(λ) → G`,
  `g ↦ lim_{t→0} t.g`, is a homomorphism with kernel `U_G(λ)`.
- Conrad–Gabber–Prasad, Proposition 2.1.8(2), printed p. 53 (PDF p. 79), with Step 2 of its
  proof, printed p. 54 (PDF p. 80). The limit map is a projector onto `Z_G(λ)`, so multiplication
  `Z_G(λ) ⋉ U_G(λ) → P_G(λ)` is an isomorphism. The decomposition statement here is the version
  of this on the points over each test scheme, for `GL_n` and a diagonal cocharacter.
