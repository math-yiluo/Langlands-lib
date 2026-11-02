# Base change of the diagonal cocharacters of `GL_n`

This module applies the general base-change results of `Langlands.GroupScheme.Dynamic.BaseChange`
to the diagonal cocharacters of `Langlands.GroupScheme.Dynamic.GeneralLinear`. Fix a morphism
`b : Spec R' ⟶ Spec R` of affine schemes and weights `e : n → ℤ`. Let
`λ_R = diagonalCocharacter n R e` be the cocharacter `t ↦ diag(t ^ e i)` of `GL_{n,R}`. The
module shows:

- after the Library isomorphism `GeneralLinear.baseChangeIso n b : (GL_{n,R})_{R'} ≅ GL_{n,R'}`,
  the base change of `λ_R` is `λ_{R'}`;
- the base changes of `P(λ_R)`, `Z(λ_R)` and `U(λ_R)` are the preimages of `P(λ_{R'})`,
  `Z(λ_{R'})` and `U(λ_{R'})` under that isomorphism;
- the block parabolic, block Levi and block unipotent subgroup functors base change in the same
  way.

The comparisons are equalities of subgroup functors of `(GL_{n,R})_{R'}`, on points over every
test scheme over `Spec R'`. The index type `n` is any `Type` with `[Fintype n]` and
`[DecidableEq n]`, and the weights are arbitrary integers.

## Sources

- Conrad, *Reductive group schemes* (2014), p. 114, the paragraph after Example 4.1.9: "It is
  immediate from the definitions that the formation of `P_G(λ)`, `U_G(λ)`, `Z_G(λ)` commutes
  with any base change on `k`".
- Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), Example 2.1.1, printed
  pp. 45–47 (PDF pp. 71–73), for the diagonal cocharacter of `GL_n` and its block subgroups.
  Their description by matrix entries makes sense over every commutative ring.

The base-change remark is about the dynamic subgroups for an abstract `𝔾_m`-action. This
module specializes it to the conjugation action of the diagonal cocharacters of `GL_n` over
affine bases. Its new content is the identification of the base-changed cocharacter with the
diagonal cocharacter over `R'`. The block subgroup functors are described by conditions on
matrix entries, so their base change is checked directly on points.

## Notation

For `x : T ⟶ (GL_{n,R})_{R'}` with `T` over `Spec R'`, the Library equivalence
`baseChangePointsEquiv b _ T x` is the corresponding point of `GL_{n,R}` over `T` viewed over
`Spec R` (`Over.map b`). `pointsEquiv n R` identifies points of `GL_{n,R}` with invertible
matrices over `Γ(T, 𝒪_T)`; this ring does not change when `T` is viewed over `Spec R`.
`SubgroupFunctor.baseChange b F` is the Library subgroup functor whose `T`-points are those `x`
with `baseChangePointsEquiv b _ T x ∈ F`. `SubgroupFunctor.comap` (from
`Langlands.GroupScheme.Dynamic.Functoriality`) is the preimage along a homomorphism.

## Results

- `pointsEquiv_comp_baseChangeIso_hom`: the matrix of `x ≫ (baseChangeIso n b).hom` over `R'`
  is the matrix of `baseChangePointsEquiv b _ T x` over `R`. This unfolds the Library
  definition of `baseChangeIso` through `isoOfPoints` and `baseChangeGLPointsEquiv`.
- `baseChangeCocharacter_diagonalCocharacter`:
  `Dynamic.baseChangeCocharacter b λ_R ≫ (baseChangeIso n b).hom = λ_{R'}`. Both sides are
  homomorphisms from `𝔾_{m,R'}`, and the proof compares them on points
  (`hom_ext_points`). On a point `t`, the base-changed cocharacter is `λ_R` on the same unit
  (`Dynamic.baseChangePointsEquiv_baseChangeCocharacter`, `Gm.baseChangeUnitsEquiv_baseChangeIso_inv`),
  so both matrices are `diag(t ^ e i)` (`pointsEquiv_diagonalCocharacter`).
- `baseChangeCocharacter_blockShapeCocharacter`: the same for the standard cocharacter of an
  ordered block shape `B : Langlands.GeneralLinear.BlockShape N`, which is the diagonal
  cocharacter for the weights `blockShapeWeight B`.
- `blockParabolic_baseChange`, `blockLevi_baseChange`, `blockUnipotent_baseChange`: for
  `F` one of `blockParabolic`, `blockLevi`, `blockUnipotent`,
  `(F n R e).baseChange b = (F n R' e).comap (baseChangeIso n b).hom`. By
  `pointsEquiv_comp_baseChangeIso_hom`, both memberships test the same matrix for the same
  entry conditions.
- `parabolic_diagonalCocharacter_baseChange`, `centralizer_diagonalCocharacter_baseChange`,
  `unipotent_diagonalCocharacter_baseChange`:
  `P(λ_R).baseChange b = P(λ_{R'}).comap (baseChangeIso n b).hom`, and likewise for `Z` and
  `U`. Proof: `Dynamic.parabolic_baseChange` identifies `P(λ_R).baseChange b` with
  `P(Dynamic.baseChangeCocharacter b λ_R)`. `Dynamic.parabolic_eq_comap_of_iso` transports it
  along `baseChangeIso n b` to the preimage of `P` of the transported cocharacter, which is
  `λ_{R'}` by `baseChangeCocharacter_diagonalCocharacter`. The same argument works for `Z` and
  `U`.

These results do not use the identification of `P(λ)`, `Z(λ)` and `U(λ)` with the block
subgroup functors. That identification is a separate statement
(`Langlands.GroupScheme.Dynamic.GeneralLinearStatement`).
