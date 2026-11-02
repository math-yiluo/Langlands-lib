# Rational characters, the centre and split components

Authors: Worker 1122 and Worker 207.

This module defines the rational characters `X^*(G)_k` of a group scheme, with
restriction along homomorphisms and evaluation on points. It also defines the
centre of a group scheme as a subgroup functor, central split tori and split
components `A_G` over a field. For the general linear group scheme it builds
the determinant character, the scalar torus `𝔾_m ⟶ GL_n` and the block
determinant characters of the block Levi subgroup schemes. All declarations are
in the namespace `Langlands.GroupScheme`; the `GL_n` items are in
`Langlands.GroupScheme.GeneralLinear`.

This module contains definitions and the elementary facts about them. The
theorems on connected reductive groups (existence and uniqueness of `A_G`,
finiteness of `X^*(G)_k`, the finite-index restriction to `A_G`, Levi
subgroups) and the `GL_n` classification are stated separately; nothing here
uses reductivity.

## Sources

- Renard, *Représentations des groupes réductifs p-adiques* (French version of
  9 July 2026), source ID `renard-2026-representations-groupes-reductifs-padiques`,
  SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
  Printed page = PDF page − 6.
  - V.2.1 (printed p.104, PDF p.110): « Notons 𝑍(G) le centre de G. » and
    « On appelle composante déployée de G un tore défini et déployé sur F,
    contenu dans le radical 𝑅(G) et maximal pour cette propriété. Si G est
    réductif, une composante déployée de G est alors un tore déployé maximal
    dans le centre de G. »
  - V.2.2 (printed p.105, PDF p.111): « soit 𝑋^∗(G) le groupe de ses
    caractères algébriques (c'est-à-dire le groupe des morphismes algébriques
    définis sur F̄ de G dans le groupe multiplicatif G_𝑚). On note 𝑋^∗(𝐺) le
    sous-groupe de 𝑋^∗(G) des caractères définis sur F, et on l'appelle groupe
    des caractères rationnels de G ».
- Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
  Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), source ID
  `waldspurger-2003-plancherel`, SHA-256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
  Printed page = PDF page + 234.
  - I.1 (printed pp.238–239, PDF pp.4–5): « Si H est un groupe algébrique, on
    note Rat(H) le groupe des caractères algébriques de H définis sur F. » and
    « on note A_M le plus grand tore déployé dans le centre de M ».

## Rational characters and restriction

Throughout, `S` is a scheme and `G H K : GroupScheme S` (the published
`Grp (Over S)`).

- `rationalCharacters G` is the published `HomAdd G (Gm S).toGrp`, that is
  `Additive (G ⟶ (Gm S).toGrp)`: the homomorphisms of group schemes
  `G ⟶ 𝔾_{m,S}` over `S`. The group law is the pointwise product of values in
  the commutative group object `𝔾_m`, written additively. Over
  `S = Spec k` these are the homomorphisms `G ⟶ 𝔾_m` of group schemes over
  `k`, so they are the characters defined over `k`: Renard's `X^*(G)_k`
  (written `𝑋^∗(𝐺)` in V.2.2) and Waldspurger's `Rat(G)`.
- `rationalCharacters.toMul_add`, `toMul_zero`: the sum is the pointwise
  product and zero is the constant `1`. `rationalCharacters.comp_add` and
  `comp_zero` state the same on a point `x : T ⟶ G.X`.
- `rationalCharacters.equivCharacterLattice T`: for `T : CommGroupScheme S`,
  `rationalCharacters T.toGrp ≃+ characterLattice T`, the identity of the
  published character lattice `X^*(T) = T ⟶ Gm S`. The two additive groups are
  definitionally the same. `groupHom_equivCharacterLattice` says that
  `CommGroupScheme.groupHom` of the lattice element is the character.
- `characterRestrict f : rationalCharacters G →+ rationalCharacters H`, for
  `f : H ⟶ G`, is precomposition `χ ↦ f ≫ χ` (`characterRestrict_apply`).
  `characterRestrict_id` and `characterRestrict_comp` give
  `characterRestrict (𝟙 G) = id` and
  `characterRestrict (g ≫ f) = (characterRestrict g).comp (characterRestrict f)`.

## Evaluation on points

- `characterEval χ T : (T ⟶ G.X) →* (Γ(T.left, ⊤))ˣ`, for every test object
  `T : Over S`, sends a point `x` to `Gm.pointsEquiv S T (x ≫ χ)`, the global
  unit of `T` given by the published identification of the points of `𝔾_m`.
  `characterEval_apply` is this formula.
- `characterEval_naturality`: for `a : T' ⟶ T`, the value at `a ≫ x` is the
  image of the value at `x` under the unit map of `a.left.appTop`.
- `characterEval_add`, `characterEval_zero`, `characterEval_zsmul`: the value
  of `χ + ψ` is the product of the values, of `0` is `1`, and of `m • χ` is
  the `m`-th power. `characterEvalHom T` is the resulting additive map
  `rationalCharacters G →+ Additive ((T ⟶ G.X) →* (Γ(T.left, ⊤))ˣ)`.
- `characterEval_characterRestrict`: `(χ ∘ f)(x) = χ(f(x))`.
- `rationalCharacters.ext_characterEval`: two characters with the same values
  on all points over all test objects are equal.

### Points over `Spec k`

For a commutative ring `k` and `G H : GroupScheme (Spec (CommRingCat.of k))`:

- `rationalPoints G` is `Over.mk (𝟙 (Spec k)) ⟶ G.X`, the group `G(k)` of
  sections with the pointwise law, as in the task conventions.
  `rationalPoints.map f : H(k) →* G(k)` is composition with `f : H ⟶ G`
  (`rationalPoints.map_apply`).
- `rationalCharacterEval χ : G(k) →* kˣ` is `characterEval` on the test object
  `Spec k` followed by the unit map of `Γ(Spec k, 𝒪) ≅ k` (`Scheme.ΓSpecIso`);
  `rationalCharacterEval_val` is this formula. `rationalCharacterEval_apply`
  identifies it with the published `Gm.affinePointsEquiv` applied to `g ≫ χ`.
- `rationalCharacterEval_add`, `rationalCharacterEval_zero`: the evaluation is
  additive in `χ`, giving `rationalCharacterEvalHom :
  rationalCharacters G →+ Additive (G(k) →* kˣ)`
  (`rationalCharacterEvalHom_apply`).
- `rationalCharacterEval_characterRestrict`: evaluation on `k`-points is
  compatible with restriction.

## The centre

- `center G : SubgroupFunctor G`. A point `g : T ⟶ G.X` lies in
  `(center G).carrier T` when for every `a : T' ⟶ T` and every point
  `h : T' ⟶ G.X`, the restriction `a ≫ g` commutes with `h` (`mem_center`).
  This is the subgroup functor of the centre `Z(G)` of Renard V.2.1: a point
  is central when it commutes with all points after every change of test
  object. The `comp_mem` field holds because the condition already quantifies
  over all `T' ⟶ T`.
- `commute_of_mem_center`: a central point commutes with every point over the
  same test object.
- `center_carrier_le_center G`: over `Spec k`, the `k`-points of `center G`
  lie in `Subgroup.center (rationalPoints G)`.
- `IsCentral i`, for `i : H ⟶ G` over any base, says that `x ≫ i` lies in
  `center G` for every point `x` of `H` over every test object.
  `IsCentral.comp` says centrality is preserved by precomposition.
  `IsCentral.map_mem_center` and `IsCentral.range_le_center`: over `Spec k`,
  the image `(rationalPoints.map i).range` of `H(k)` lies in the centre of
  `G(k)`.

## Central split tori and split components

Here `k` is a field, `G : GroupScheme (Spec (CommRingCat.of k))` and
`A : CommGroupScheme (Spec (CommRingCat.of k))`.

- `IsCentralSplitTorus i`, for `i : A.toGrp ⟶ G`, is
  `IsSplitSubtorus i ∧ IsCentral i`. The published `IsSplitSubtorus i` says
  that `A` is a split torus and `i` is a closed immersion (a closed subgroup).
  So `i` is a split subtorus of `G` contained in the centre.
- `IsSplitComponent i` holds when `IsCentralSplitTorus i` holds and, for every
  `A'`, every `i' : A'.toGrp ⟶ G` with `IsCentralSplitTorus i'` and every
  `f : A.toGrp ⟶ A'.toGrp` with `f ≫ i' = i`, the map `f` is an isomorphism.
  This is maximality for inclusion among central split tori, in the pattern of
  the published `IsMaximalSplitTorus`.
- Projections: `IsCentralSplitTorus.isSplitSubtorus`,
  `IsCentralSplitTorus.isCentral`, `IsSplitComponent.isCentralSplitTorus`.
- `IsCentralSplitTorus.range_le_center`: for a central split torus
  `i : A ⟶ G`, the image of `A(k)` in `G(k)` lies in `Subgroup.center G(k)`.

## The general linear group

Here `n` is a finite type with decidable equality and `R : CommRingCat`. The
published `GeneralLinear.groupScheme n R` has points
`GeneralLinear.pointsEquiv n R T : (T ⟶ GL_n.X) ≃* GL n Γ(T.left, ⊤)`.

- `GeneralLinear.map_scalar` restates Mathlib's
  `Matrix.GeneralLinearGroup.map_scalar` with the unit map written as
  `Units.map f.toMonoidHom`, the form used by `Gm.pointsEquiv_naturality`.

### The determinant character

- `determinantPoints n R T` is the determinant on `T`-points, with values in
  the points of `𝔾_m`; `determinantPoints_naturality` is its naturality.
- `determinantCharacter n R : rationalCharacters (groupScheme n R)` is the
  homomorphism `GL_n ⟶ 𝔾_m` with these points (the published `homOfPoints`).
- `comp_determinantCharacter` and `characterEval_determinantCharacter`: on a
  point `x`, `characterEval (determinantCharacter n R) T x` is
  `Matrix.GeneralLinearGroup.det (pointsEquiv n R T x)`.

### The scalar torus

- `scalarPoints n R T` sends a unit `t` to the scalar matrix `t · 1`
  (`Matrix.GeneralLinearGroup.scalar`); `scalarPoints_naturality` uses
  `map_scalar`.
- `scalarTorus n R : (Gm (Spec R)).toGrp ⟶ groupScheme n R` is the
  homomorphism with these points. `pointsEquiv_scalarTorus` is its value on
  points. `scalarTorus_eq_diagonalCocharacter` identifies it with the
  published diagonal cocharacter `diagonalCocharacter n R (fun _ => 1)`.
- `isCentral_scalarTorus`: the scalar torus is central, for every `n` and `R`.
  The proof uses Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`
  on `GL n Γ(T'.left, ⊤)`.

#### The scalar torus is a closed subgroup

- `mem_range_scalar_iff`: an invertible matrix is scalar exactly when its
  off-diagonal entries vanish and its diagonal entries are equal.
- `scalarIdeal n R` is the ideal of the published coordinate ring of `GL_n`
  generated by the coordinates `x_ij` with `i ≠ j` and the differences
  `x_ii - x_jj`. `classify_eq_zero_iff_scalar`: the algebra map classifying an
  invertible matrix `g` kills `scalarIdeal n R` exactly when `g` is scalar.
- `scalarSubgroup n R A` is the subgroup of scalar matrices in the points
  `(functor n R).obj A` over an `R`-algebra `A` (`mem_scalarSubgroup`), and
  `isCutOutBy_scalarIdeal` says, in the published
  `Corepresented.IsCutOutBy` form, that `scalarIdeal n R` cuts out these
  subgroups.
- `pointsEquiv_cutHom`: for any subgroup family cut out by an ideal, the
  published inclusion `Corepresented.cutHom` acts on points by forgetting
  membership.
- For nonempty `n`: `scalar_injective` (a unit is determined by its scalar
  matrix), `scalarEquiv n R A : Aˣ ≃* scalarSubgroup n R A`
  (`scalarEquiv_val`), the points equivalence `scalarCutPointsEquiv n R T`
  between `𝔾_m` and the cut-out group scheme
  (`pointsEquiv_scalarCutPointsEquiv`, `scalarCutPointsEquiv_naturality`), and
  the resulting isomorphism `scalarIso n R` of `𝔾_m` with the closed subgroup
  scheme of scalar matrices (the published `isoOfPoints`).
  `scalarTorus_eq_scalarIso_comp`: `scalarTorus n R` is `scalarIso n R`
  followed by the closed subgroup inclusion.
- `isClosedSubgroup_scalarTorus n R`: for nonempty `n` and every `R`, the
  scalar torus is a closed subgroup (`IsClosedSubgroup`).
- `isCentralSplitTorus_scalarTorus n k`: for nonempty `n` over a field `k`,
  the scalar torus is a central split torus. `𝔾_m` is a split torus by the
  published `isSplitTorus_gm`.

For empty `n`, `GL_n` is the trivial group scheme `Spec R`. When `R` is a
nonzero ring, in particular over a field, `𝔾_m ⟶ Spec R` is not a closed
immersion, since `R ⟶ R[t, t⁻¹]` is not surjective. (Over the zero ring every
scheme here is empty and the map is an isomorphism.) So the closed-subgroup
result, which is stated for every `R`, assumes `Nonempty n`, and so does the
central-split-torus result over a field.

### Block determinant characters

Here `B : Langlands.GeneralLinear.BlockShape N` is a published block shape of
`N`, with blocks `i : Fin B.length` of size `B.size i` and coordinate
inclusions `B.index i : Fin (B.size i) ↪ Fin N`. The published block Levi
subgroup scheme `blockLeviScheme (Fin N) R (blockShapeWeight B)` is cut out of
`GL_N` by the block diagonal condition, with inclusion `blockLeviHom`.

- `blockDet B i A : blockLeviSubgroup A (blockShapeWeight B) →* Aˣ`, for a
  commutative ring `A`, is the determinant of the `i`-th diagonal block. It is
  built from the published identification
  `blockLeviSubgroup_blockShapeWeight` with the block diagonal subgroup and the
  published `B.leviEquiv A` with the product of the `GL (B.size j) A`.
  `blockDet_val`: its value is
  `Matrix.det (g.submatrix (B.index i) (B.index i))`. `blockDet_map`: it
  commutes with change of coefficients.
- `blockDetPoints R B i T` is the `i`-th block determinant on `T`-points
  (`pointsEquiv_blockDetPoints`, `blockDetPoints_naturality`).
- `blockDeterminantCharacter R B i :
  rationalCharacters (blockLeviScheme (Fin N) R (blockShapeWeight B))` is the
  character with these points (`comp_blockDeterminantCharacter`).
- `characterEval_blockDeterminantCharacter`: on a point `x`, its value is the
  determinant of the `i`-th diagonal block of the matrix
  `pointsEquiv (Fin N) R T (x ≫ blockLeviHom)` in `GL_N`.

## Provenance and scope

The sources work with linear algebraic groups over a non-archimedean local
field `F`. The definitions here are scheme-theoretic forms of the same
objects. The added generality is derived:

- Characters, restriction, evaluation, the centre and `IsCentral` are defined
  for every group scheme over every base scheme. Over `Spec k` a homomorphism
  of group schemes over `k` is a character defined over `k`, which is
  Renard's `X^*(G)_k` and Waldspurger's `Rat(G)`. Renard's larger group of
  characters over `F̄` is not defined here.
- `rationalPoints` and `rationalCharacterEval` are defined over every
  commutative ring `k`; the field case is the one the sources use.
- Renard's primary definition of the split component is a maximal split torus
  in the radical `R(G)`. For reductive `G` he notes that this is the same as a
  maximal split torus in the centre, which is Waldspurger's definition of
  `A_M`. `IsSplitComponent` uses the centre form for every group scheme over a
  field. "Maximal" (Renard) and "le plus grand" (Waldspurger) are expressed by
  factorization of morphisms, as for the published `IsMaximalSplitTorus`.
  Existence and uniqueness of split components for connected reductive groups
  are not proved here.
- The determinant, scalar torus and block determinant constructions are
  defined over every commutative ring `R`. The scalar torus is central for
  every `n` and `R`, and a closed subgroup for nonempty `n` and every `R`.
  These standard `GL_n` objects are internal constructions for the `GL_n`
  case of the split component and character statements.

Credit: Worker 207's draft of this module supplied the design of `center`,
`IsCentral`, `rationalPoints.map` and evaluation on `k`-points through
`Gm.affinePointsEquiv`, and parts of this Markdown.
