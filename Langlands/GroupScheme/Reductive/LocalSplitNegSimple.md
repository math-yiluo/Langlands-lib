# Right translation of big-cell points by negative simple root points

This module proves the published `LocalSplitWeylNegSimpleStatement` (module
`LocalSplitIsomorphismAssembly`) from three statements:

- `LocalSplitRankOneNormalStatement`;
- `LocalSplitRankOneBruhatStatement`;
- `LocalSplitWeylConjugationStatement`.

None of them is proved here. The module imports `LocalSplitNegativeLaws` and
`LocalSplitRankOneBruhatStatement`.

Notation:

- `rootPoint v Z x` is the point of `v : 𝔾ₐ ⟶ G` at `x`.
- `orderedProduct v e Z w` is the ordered product of root points along an index family `e`.
- `cellMap i v neg pos` is the big-cell map `(w⁻, t, w⁺) ↦ N(w⁻) · i(t) · U(w⁺)`.
  Here `N` and `U` are the ordered products along `neg` and `pos`.
- `mkCellPoint Z w⁻ t w⁺` is the cell point with these coordinates, and `negCoord`,
  `torusCoord`, `posCoord` read them off.
- `torusChar χ Z t` is the value of the character `χ` at a torus point `t`.
- `cocharPoint ν Z l` is the torus point `ν(l)` of a unit `l`.
- `-a` is the index `P.reflectionPerm a a`, `n_a = rootWeylPoint P u a`, and `v`, `v'` are the
  Weyl families of `u`, `u'`.

## Main statement

`LocalSplitWeylNegSimpleReductionStatement.{u}` is the proposition

`LocalSplitRankOneNormalStatement.{u} → LocalSplitRankOneBruhatStatement.{u} →
LocalSplitWeylConjugationStatement.{u} → LocalSplitWeylNegSimpleStatement.{u}`.

The module proves it as `localSplitWeylNegSimpleReduction`, by
`localSplitWeylNegSimple_of_rankOne`, which has the same type.

## Results

**Fields.**
- `infinite_of_isSepClosed`: a separably closed field is infinite.
- `exists_ne_zero_pow_four_ne_one`: an infinite field has an element `l ≠ 0` with `l⁴ ≠ 1`.

**Products and weights** (namespace `Langlands.GroupScheme.LocalSplitCell`, for a family `u`,
torus-equivariant with characters `ch` (`TorusEquivariant`), whose cell map is an open
immersion):
- `orderedProduct_specHom` pulls back an equality of ordered products along a ring map.
- `coord_eq_zero_of_weight`: let `ν` pair negatively with the characters at `neg`, and let
  `ω` be a cocharacter. Take an ordered product along `e` whose characters pair positively
  with `ν` and non-negatively with `ω`, and whose factors of `ω`-weight zero alone multiply to
  `1`. Written as an ordered product along `pos`, it has zero coordinate at every position
  whose character pairs non-positively with `ω`. This holds over every ring.
- `orderedProduct_eq_list_prod`, `orderedProduct_inv_eq_list_prod`: an ordered product and its
  inverse as products of lists of root points.
- `exists_orderedProduct_mul_list`: an ordered product along `pos`, multiplied by a list of
  root points pairing positively with `ν`, is again one (over local rings).
- `torus_mul_comp_cellMap`, `comp_cellMap_mul_torus'`: left and right multiplication of a cell
  point by a torus point, with explicit coordinates.
- `orderedProduct_cons`, `conj_prod_ofFn`: products along `Fin.cons`, and conjugation of a
  list product.
- `cell_mul_negSimple_eq`: a computation in one group. Suppose
  - `U(posCoord x) = u_a(c) · U(w₁)` and `u_{-a}(1) U(w₁) u_{-a}(-1) = U(w₂)`;
  - `u_a(c) u_{-a}(-1) = u_{-a}(d⁻¹ · (-1)) a^∨(d) u_a(d⁻¹ c)`;
  - the torus factor of `x` moves `u_{-a}(d⁻¹ · (-1))` to `u_{-a}(χ d⁻¹ · (-1))`;
  - `N(negCoord x) u_{-a}(χ d⁻¹ · (-1)) = N(z)` and `u_a(d⁻¹ c) U(w₂) = U(w₃)`.

  Then `(x ≫ cellMap) · u_{-a}(-1)` is the cell point with coordinates `z`,
  `torusCoord x · a^∨(d)` and `w₃`.

**Weyl families** (setting of `LocalSplitWeylCommutatorReduction`: `R` local,
`IsNormalSimpleData` for `G` and `H`, `WeylConjugationRelations`, a simple root `a`, an
enumeration `neg` of the non-positive roots and an enumeration `pos` of the positive roots by
increasing height, with `a` at position `pa`):
- `IsNormalSimpleData.exists_weight`: there is a cocharacter `ω` whose pairing with a positive
  root `α` is non-negative, and zero exactly for `α = a`.
- `IsNormalSimpleData.coord_eq_zero_of_simple`: in an ordered product of positive Weyl-family
  points whose factors at `a` alone multiply to `1`, written along `pos`, the coordinate at `a`
  vanishes.
- `WeylConjugationRelations.conj_points`, `inv_conj_points`: on points,
  `n_c v_d(x) n_c⁻¹ = v_{s_c d}(κ x)` and `n_c⁻¹ v_δ(x) n_c = v_{s_c δ}(κ' x)` with units
  common to `G` and `H`.
- `negSimple_conj_orderedProduct`: if `w pa = 0`, then
  `u_{-a}(x) · U(w) · u_{-a}(-x) = U(w'')` with `w'' pa = 0`, with the same `w''` in `G` and
  `H`.
- `split_simple_orderedProduct`: `U(w) = u_a(w pa) · U(w₁)` with `w₁ pa = 0`, with the same
  `w₁` in `G` and `H`.
- `IsNormalSimpleData.exists_negProduct_mul`, `exists_negProduct_mul_list`,
  `exists_posProduct_mul_list`: products along `neg` (or `pos`) times non-positive (or
  positive) Weyl-family points are again such products.
- `torusChar_comp_exponentIso_hom`: moving a torus point by the exponent automorphism `e`
  changes a character `m` into `e m`. `coPairing_neg`: `⟨-χ, ν⟩ = -⟨χ, ν⟩`.
- `IsNormalSimpleData.false_of_weylPoint_mem`: over a local ring with a unit `l₀`,
  `l₀⁴ ≠ 1`, no element `N(w⁻) · i(T) · n_a · U(w⁺)` is a cell point.
- `IsNormalSimpleData.rootPoint_weylFamily_neg`: `v_{-a}(y) = u_{-a}(-y)`.
- `IsNormalSimpleData.rootPoint_one_mul_neg`: `u_a(1) u_{-a}(-1) = n_a u_a(-1)`.
- `negSimple_transfer`: with `RankOneBruhat` for `G` and `H` at `a`, over a local ring `A` with
  separably closed residue field, if `(x ≫ cellMap i v neg pos) · u_{-a}(-1) =
  y ≫ cellMap i v neg pos`, then the same holds for `i'`, `v'` and `u'`.

## Proof

**Weights.** `coord_eq_zero_of_weight` deforms the product over `B[X]`, scaling the `k`-th
coordinate by `X` to its `ω`-weight. Its coordinates along `pos` are polynomials vanishing at
`X = 0`, where only the weight-zero factors survive and multiply to `1`. Over Laurent
polynomials, conjugation by the torus point `ω(X)` (imported
`torus_mul_orderedProduct_mul_inv`) identifies the deformed product. Comparing coordinates
(`orderedProduct_pos_injective`) shows that a coordinate of non-positive weight is
`X^d` times a polynomial vanishing at `0`, hence zero. The cocharacter of `exists_weight` is
`2ν - ⟨a, ν⟩ a^∨`, with `ν` the height cocharacter. It pairs with `α` to a positive multiple
of `ht(α) + ht(s_a α)` (imported `coPairing_root_coroot` and `height_reflectionPerm_of_mem`),
and `s_a` permutes the positive roots other than `a`.

**Conjugation of the unipotent radical of `a`.** By `RankOneNormal`,
`u_{-a}(x) = n_a u_a(-x) n_a⁻¹`. In `negSimple_conj_orderedProduct`:
- conjugation by `n_a⁻¹` moves the factors of `U(w)` to positive roots, with common units
  (`inv_conj_points`);
- multiplying by `u_a(∓x)` and conjugating by `n_a` again (`conj_points`) gives products of
  positive root points;
- these are rewritten along `pos` with the same coordinates in `G` and `H` by the positive
  laws (`posGood_rootPoint_of_base`, `PosGood.exists_eq`);
- `coord_eq_zero_of_simple` shows that the coordinates at `a` vanish.

`split_simple_orderedProduct` multiplies `U(w)` on the left by `u_a(-w pa)` in the same way.

**The unit case.** If `1 - c` is a unit, with `c` the coordinate of `x` at `a`, then:
- `RankOneBruhat` with `x = c`, `y = -1` gives the rank-one factorization;
- the torus equivariance of `u_{-a}` gives the character `χ`;
- `exists_negProduct_mul`, `rootPoint_weylFamily_neg` and `negativeLaws` give the negative
  factor with the same coordinates in `G` and `H`;
- the positive laws give the positive factor.

`cell_mul_negSimple_eq` computes the translate in both groups. The relation in `G` and the
injectivity of the cell map identify `y` with the computed cell point, so the relation holds
in `H`.

**The non-unit case does not occur.** Pass to the residue field `K` of `A`, which is infinite
(`infinite_of_isSepClosed`). There the coordinate at `a` is `1`. By
`rootPoint_one_mul_neg`, the relation pulled back to `K` gives a cell point equal to
`N · i(T) · n_a · U`, contradicting `false_of_weylPoint_mem`.

`false_of_weylPoint_mem` uses the torus point `t = a^∨(l₀)`. Since `n_a t n_a⁻¹ = s_a(t)`
(`IsWeylPoint`), the element `E = N · i(T) · n_a · U` satisfies
`E · t = s_a(t) · K` for a cell point `K` with the torus coordinate of `E`. The point `K` is
built with the list lemmas. Comparing torus coordinates of the cell points `E · t` and
`s_a(t) · K` gives `t = s_a(t)`. Evaluating the character `a` gives `l₀² = l₀⁻²`
(`torusChar_comp_exponentIso_hom`, `torusChar_cocharPoint`, `⟨a, a^∨⟩ = 2`).

**The main theorem.** The statements give `IsNormalSimpleData` and `RankOneBruhat` for `G` and
`H` and `WeylConjugationRelations`, and `negSimple_transfer` gives `NegSimpleRelations`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. In SGA 3, Exp. XXIII, Theorem 2.1 and Proposition 2.1.2, a morphism on the big cell
`Ω` defined by root and torus data extends to a homomorphism once it is generically
multiplicative; the relations proved here play that role for right translation by the
negative simple root points. The rank-one factorization is SGA 3, Exp. XX, Lemma 6.2.2. The
weight argument for the vanishing coordinate, the transfer through
common Weyl-conjugation units, and the exclusion of the non-unit case through the residue
field are this module's own. The three assumed statements are not proved here.
