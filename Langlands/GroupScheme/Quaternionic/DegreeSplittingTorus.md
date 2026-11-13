# The Witt torus of `SU(D, h)` over a separable closure

Lean module: `Langlands.GroupScheme.Quaternionic.DegreeSplittingTorus`
(namespace `Langlands.GroupScheme.Quaternionic.DegreeSplitting`).

Setting: `D` a central division algebra, finite-dimensional over a field `K`, of degree `δ`
(`finrank K D = δ ^ 2`); `σ` an involution of the first kind of `D` whose symmetric elements
have dimension `δ (δ + 1) / 2`; `H ∈ M_m(D)` (`m > 0`) invertible and trace-valued
`σ`-antihermitian, of Witt index `r = σ.wittIndex H`; `m δ = 2 N`. `K_s = SeparableClosure K`.
`σ.symplecticGroup H` is the group scheme `SU(D, h)` of `Quaternionic.GroupSchemes`.

This internal module provides the general-degree splitting needed for
`TypeCDistinguishedVerticesStatement`. Its main theorem identifies the base change to `K_s` of
the Witt torus of `σ.symplecticGroup H` with an explicit subtorus of the diagonal torus of
`Sp_{2N}`.

## Main theorem

`exists_wittTorus_splitting hD hσ H hH hu hN`: `r δ ≤ N`, and there are

* a homomorphism `s : 𝔾ₘ^r → σ.symplecticGroup H` (split torus `splitTorus` on
  `ULift (Fin r)` over `Spec K`) that is a maximal split torus (`IsMaximalSplitTorus s`), and
* an isomorphism `Φ : σ.baseChangeSymplecticGroup H (L := K_s) ≅ SymplecticMatrix.groupScheme
  (Fin N) K_s`,

such that

`(splitTorus.baseChangeIso _ _).inv ≫ (GroupScheme.baseChange _).map s ≫ Φ.hom =
  CommGroupScheme.groupHom (blockTorusHom K_s δ r N) ≫ SymplecticMatrix.diagonalTorus (Fin N) K_s`.

That is, after base change to `K_s` and `Φ`, the torus `s` is `blockTorusHom` followed by the
diagonal torus `t ↦ diag(t, t⁻¹)` of `Sp_{2N}`.

## The block exponent homomorphism

For a field `L` and `δ, r, N`:

* `blockExponent δ r N : ℤ^N → ℤ^r` (coordinates `ULift (Fin N)`, `ULift (Fin r)`) is
  multiplication by the integer matrix with entries `blockWeight δ r a k`
  (`blockWeight` from `DegreeSplittingDarboux`: `1` if `k δ ≤ a < (k + 1) δ`, else `0`).
  `blockExponent_single`: it sends `e_a` to `blockWeight δ r a`.
* `blockTorusHom L δ r N : 𝔾ₘ^r → 𝔾ₘ^N` is the Library's `splitTorus.exponentHom` of
  `blockExponent`.
* `pointsEquiv_blockTorusHom`: on points, the `a`-th coordinate of the image of `t` is the
  monomial `∏_k t_k^{blockWeight δ r a k}`. So it is `t_k` for the block `k` containing `a`,
  and `1` when `a ≥ r δ`.
* `characterCoordEquiv_blockTorusHom_comp_coordChar`: the coordinate character `e_a` of the
  diagonal torus of `Sp_{2N}` (`SymplecticMatrix.coordChar`) pulls back along `blockTorusHom`
  to the character with coordinates `k ↦ if k δ ≤ a < (k + 1) δ then 1 else 0`. The proof
  writes `coordChar a` as an exponent character, then uses
  `splitTorus.exponentHom_comp_exponentCharacter`.

## Witt weights and diagonal units

* `wittWeight_add_eq_zero`: where `wittGram HU s t ≠ 0`, `wittWeight s + wittWeight t = 0`.
  `sum_wittWeight`: the Witt weights sum to `0`. `liftedWittWeight ε i` is `wittWeight (ε i)`
  with `ULift` coordinates. `liftedWittWeight_add_eq_zero`, `sum_liftedWittWeight` and
  `exists_liftedWittWeight_eq_single` are the corresponding facts for it.
* `matrixChartR_diagRingHom`: the matrix chart of the diagonal matrix `diag(c)` of
  `R ⊗[K] M_n(D)` is the diagonal matrix with entry `c_i` at `(i, a)`.
* `map_mul_diagonal_monomial`: if `P` is homogeneous (`P a b ≠ 0 → V a = W b`), then
  `P diag(t^{W b}) = diag(t^{V a}) P` (entries of `P` mapped into the coefficient ring).
* `darbouxMatrix_weightUnits`: for `P` homogeneous for `darbouxWeight` and the Witt weights,
  with `P P' = 1`, the Darboux matrix `P Φ(u) P'` of the weighted diagonal unit
  `weightUnits (liftedWittWeight ε) t` is the diagonal matrix `diag(t^{darbouxWeight α})`.
  The weighted diagonal units and the weighted torus `symplecticTorus` are those of
  `AntihermitianSplitRankLower`.
* `monomial_neg`: `t^{-a} = (t^a)⁻¹`.

## The square over a splitting field

`baseChange_symplecticTorus_comp_splittingIso`: let `e : L ⊗[K] D ≃ₐ[L] M_δ(L)`,
`G ∈ M_m(D)`, `ε : Fin m ≃ (Fin r ⊕ Fin r) ⊕ Fin d`, and `P`, `P'` with `P P' = 1`, `P' P = 1`,
`P C Pᵀ = J` for `C = splitGram e σ G`, and homogeneous as above. Let `hG` and `hsum` be the
weight conditions for `liftedWittWeight ε`. Then the base change to `L` of
`symplecticTorus σ (liftedWittWeight ε) G hG hsum`, followed by `splittingIso` of
`DegreeSplittingIso`, equals `blockTorusHom L δ r N` followed by the diagonal torus of
`Sp_{2N}`.

Proof: compare points (`hom_ext_points`). `pointsEquiv_splittingIso_hom` computes the left side
as `P Φ(u) P'` for the unit `u` of the point. `symplecticTorus_comp` and
`pointsEquiv_comp_weightHom` identify `u` as a weighted diagonal unit, and the base-change
point of the torus is computed by `isoOfPointModels_inv`. `darbouxMatrix_weightUnits` gives
`diag(t^{darbouxWeight α})`. The right side is `diag(t^{blockWeight a}, (t^{blockWeight a})⁻¹)`
(`levi_diagonalTorusUnits`, `torusWeights`, `pointsEquiv_blockTorusHom`, `monomial_neg`).

## Maximality

`isMaximalSplitTorus_of_card_eq_wittIndex`: a closed subgroup `s : 𝔾ₘ^I → σ.symplecticGroup H`
with `|I| = σ.wittIndex H` (and `H` a unit) is a maximal split torus. If `s` factors as `a ≫ j'`
through a closed split torus `j' ≅ 𝔾ₘ^J`, then `|J| ≤ σ.wittIndex H` by `card_le_wittIndex` of
`AntihermitianSplitRankUpper`. The factor `𝔾ₘ^I → 𝔾ₘ^J` is a monomorphism, so `|I| ≤ |J|`
(`splitTorus.card_le_card_of_mono`). Hence `|I| = |J|`, and `splitTorus.isIso_of_mono_of_card_eq`
makes the factor an isomorphism.

## Proof of the main theorem

1. `CentralSimple.exists_separableClosure_matrix_chart` gives a chart
   `e : K_s ⊗[K] D ≃ M_{δ'}(K_s)` with `δ'² = finrank K D = δ²`, so `δ' = δ`.
2. `exists_wittBlockBasis` (`AntihermitianWittBlock`) gives `ε`, a unit `PW` and `HU` with
   `H' = PW H ᵗPW^σ` equal to `wittGram HU` after relabelling by `ε`. The Library's
   `symplecticGroupCongr` gives an isomorphism `c : σ.symplecticGroup H ≅ σ.symplecticGroup H'`.
   `H'` is a unit (`isUnit_apply` shows `ᵗPW^σ` is a unit).
3. `exists_wittDarboux` (`DegreeSplittingDarboux`) gives `r δ ≤ N` and homogeneous Darboux
   matrices `P`, `P'` for `splitGram e σ H'`.
4. `s = symplecticTorus σ (liftedWittWeight ε) H' hG hsum ≫ c.inv` and
   `Φ = (baseChange).mapIso c ≪≫ splittingIso e σ H' P P' …`.
5. `s` is closed (`isClosedSubgroup_symplecticTorus`, transported along `c.inv` by
   `isClosedSubgroup_comp_iso`) of rank `r`, hence maximal by
   `isMaximalSplitTorus_of_card_eq_wittIndex`.
6. In the square, the base change of `c.inv ≫ c.hom` cancels (`Functor.map_comp`,
   `Iso.inv_hom_id`, `Functor.map_id`). What remains is
   `baseChange_symplecticTorus_comp_splittingIso`.

## Provenance

This is the standard description of a maximal split torus of `SU(D, h)` for `D` of degree `δ`
and `h` antihermitian with respect to an orthogonal-type involution: over a splitting field the
group is `Sp_{2N}` with `2N = m δ`, and the Witt torus of rank `r` acts on the `k`-th hyperbolic
pair through `δ` equal diagonal coordinates (Tits 1966, Table II, type `C_n`, where the
distinguished vertices are `δ, 2δ, …, rδ`). The proofs were written for this module. They use
the Library's group-scheme, split-torus and symplectic-matrix infrastructure, and the modules
`AntihermitianSplitRankLower`, `AntihermitianSplitRankUpper` (copied from Task 5986) and
`AntihermitianWittBlock`, `DegreeSplittingDarboux` and `DegreeSplittingIso`.
