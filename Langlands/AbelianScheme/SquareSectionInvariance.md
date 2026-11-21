# Sections of `L ⊗ L` from translates, and generic invariance of their zero sets

Helper module for the core proof of
`Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationStatement`. Mumford,
*Abelian Varieties*, §17 (printed pp.163–164), uses triples of translates of a
reduced divisor with parameters summing to zero, giving a member of `|3D|`.
In the point argument he fixes the first parameter and varies the second to
avoid both auxiliary supports at the comparison point. The constructions here
adapt that argument: `pairSection` uses the square identity at `(a,a⁻¹)` to
obtain sections of `L ⊗ L`, and `squarePairSection` uses `tripleIso hsq a a`
to multiply a translate of any section of `L ⊗ L` by one translate of a fixed
section of `L`. The two generic vanishing implications are for this adapted
square system, not for Mumford's reduced divisor.

Setting: `G : Grp (Over (Spec K))`, `L` a line bundle on `G.X.left` satisfying the
theorem of the square `SquareFor G L` (published in
`Langlands/AbelianScheme/SeparatingLineBundle/Assembly`), `s` a section of `L`.
Rational points of `G` (morphisms `Over.mk (𝟙 _) ⟶ G.X`) are written
multiplicatively; `τ_a` is the published `translation G a`, and `transLB G L a`,
`transSection G L s a` are the pulled-back bundle and section. `cubeLB G L` is the
Library's `(L ⊗ L) ⊗ L`.

## Declarations

- `squareLB G L`: the line bundle `L ⊗ L` (`tensorLB L L`).
- `transSquareIso`: `τ_c^*(L ⊗ L) ≅ τ_c^* L ⊗ τ_c^* L`, the pullback-tensor comparison.
- `pairIso hsq a`: `τ_a^* L ⊗ τ_{a⁻¹}^* L ≅ L ⊗ L`, from the theorem of the square and
  `τ_{a a⁻¹} = τ_1`.
- `pairSection s hsq a`: the section `τ_a^* s ⊗ τ_{a⁻¹}^* s` of `L ⊗ L`, transported by
  `pairIso`.
- `vanishesAlong_pairSection_point_iff`: at a rational point `d`, the pair section
  vanishes iff `s` vanishes at `a d` or at `a⁻¹ d`.
- `squarePairIso hsq a`: `τ_{(a a)⁻¹}^* L ⊗ τ_a^*(L ⊗ L) ≅ (L ⊗ L) ⊗ L`, composed of
  `transSquareIso` and the Library's `tripleIso hsq a a`.
- `squarePairSection s hsq σ a`: for a section `σ` of `L ⊗ L`, the section
  `τ_{(a a)⁻¹}^* s ⊗ τ_a^* σ` of `(L ⊗ L) ⊗ L`.
- `vanishesAlong_squarePairSection_point_iff`: at a rational point `d` it vanishes iff
  `s` vanishes at `(a a)⁻¹ d` or `σ` vanishes at `a d`.
- `vanishesAlong_squarePairSection_tangent_iff`: for a tangent vector `t` at `d`
  (`IsTangentVectorAt`) with `s((a a)⁻¹ d) ≠ 0`, it vanishes along `t` iff `σ`
  vanishes along `t ≫ τ_a`.
- `vanishesAlong_square_of_not_separates`: if every section of `(L ⊗ L) ⊗ L` vanishing
  at `x₀` vanishes at `x₁`, then for every rational `a` with `s((a a)⁻¹ x₁) ≠ 0` and
  every section `σ` of `L ⊗ L`, `σ(a x₀) = 0` implies `σ(a x₁) = 0`.
- `vanishesAlong_square_translate_tangent_of_not_separates`: if every section of
  `(L ⊗ L) ⊗ L` vanishing at `x₀` vanishes along a tangent vector `t` at `x₀`, then for
  every rational `a` with `s((a a)⁻¹ x₀) ≠ 0` and every section `σ` of `L ⊗ L`,
  `σ(a x₀) = 0` implies that `σ` vanishes along `t ≫ τ_a`.
- `exists_squareSection_not_vanishesAlong`, `exists_cubeSection_not_vanishesAlong`:
  for `K` algebraically closed, `G` commutative, locally of finite type and
  irreducible, if `s` is nonzero at some rational point then `L ⊗ L` and
  `(L ⊗ L) ⊗ L` have no rational base point.

## Proofs

The vanishing criteria rewrite through `vanishesAlong_mapIso_iff` (isomorphisms of
line bundles do not change vanishing), `vanishesAlong_tensor_field_iff` (a tensor
product of sections vanishes at a rational point iff one factor does),
`vanishesAlong_transSection_iff` and `left_comp_translation`; the tangent criterion
uses `vanishesAlong_tensor_left_iff`, which removes a factor that is a unit near the
base point (`mem_trivializationOpen_of_isTangentVectorAt`).

For the two invariance statements: `σ(a x₀) = 0` makes `squarePairSection s hsq σ a`
vanish at `x₀`, so by hypothesis it vanishes at `x₁` (resp. along `t`); its first
factor `s((a a)⁻¹ x₁)` (resp. `s((a a)⁻¹ x₀)`) is nonzero, so the second factor
vanishes there.

For base points at `d`: the Library's `exists_good_second` (with `a = 1`) gives `b`
with `s(b d) ≠ 0` and `s(b⁻¹ d) ≠ 0`, so `pairSection s hsq b` is nonzero at `d`; the
Library's `exists_good_pair` gives `a, b` for which `tripleSection s hsq a b` is
nonzero at `d` (`vanishesAlong_tripleSection_point_iff`).
