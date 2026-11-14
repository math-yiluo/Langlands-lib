# The rank-one isomorphism theorem from root groups and the open cell

Author: Worker 1388.

Module `Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction`. This is an
internal supporting unit. It proves

`splitRankOneCommonTorusIsomorphism_of_rootCell :
  SplitRankOneRootCellStatement.{u} → SplitRankOneCommonTorusIsomorphismStatement.{u}`.

So the Isomorphism Theorem in semisimple rank at most one, for two groups with a common
split maximal torus, follows from the existence of root groups whose open cell satisfies
the rank-one relation. The theorem assumes `SplitRankOneRootCellStatement` and does not
prove it. Its other inputs are the gluing criterion of `OpenCellGluing` and the rank-zero
case `exists_iso_of_roots_eq_empty` of `SplitRankZeroIsomorphism`.

## Definitions (namespace `Langlands.GroupScheme.RootCell`)

- `Ga k` is the additive group `VectorGroup.groupScheme (CommRingCat.of k) 1`.
  `crd a ∈ Γ(Z.left, ⊤)` is the coordinate of a point `a : Z ⟶ 𝔾ₐ`, and `pt x` is the
  point with coordinate `x` (`crd_pt`). The shared `crd_injective` theorem, moved
  unchanged from `SplitRankOneRootCellUniversal`, identifies points with equal coordinates.
- `Cell T` is `𝔾ₐ ⊗ (T.X ⊗ 𝔾ₐ)`, the source of `Dynamic.tripleCellMultiplication`.
  `eq_lift` writes a point of `Cell T` as `lift m (lift t p)`.
- `coU χv u : Z ⟶ T.X` is the point `χv(u)` of `T`, for a cocharacter `χv` and a unit `u`.
- `cellProd χ χv m p m' p' t t' u : Z ⟶ Cell T` is the point with components
  `m · χ(t)⁻¹ u⁻¹ m'`, `t · χv(u) · t'` and `χ(t')⁻¹ u⁻¹ p · p'` (written additively for
  the `𝔾ₐ` components). It depends only on `χ`, `χv` and the input points, not on any
  group `G`.
- `IsRootCell i χ χv xp xm` is a structure with five fields. They are the five clauses
  of the conclusion of `SplitRankOneRootCellStatement`, for the character `χ` in place
  of `P.root r` and the cocharacter `χv` in place of `P.coroot r`.
- `unitPt T` and `torusPt T` are the points `(1, 1, 1)` and `(1, 𝟙, 1)` of the cell.
  They map to `1` and to `i` (`unitPt_comp`, `torusPt_comp`).

## The implemented proof

Write `Ω(m, t, p) = xm(m) i(t) xp(p)` for the cell map `Dynamic.tripleCellMultiplication`.
Let `D : IsRootCell i χ χv xp xm`.

1. **`IsRootCell.isUnit_of_mul_eq`.** Suppose `Ω(m, t, p) Ω(m', t', p') = Ω(c)`. Then
   `xp(p) xm(m') = i(t)⁻¹ xm(m)⁻¹ Ω(c) xp(p')⁻¹ i(t')⁻¹`. Moving `i(t)⁻¹` and `i(t')⁻¹`
   across the root groups with the conjugation fields shows that the right side is a cell
   point. Lean names the cell coordinates and uses `group`. The `exists_iff` field then
   makes `1 + crd p · crd m'` a unit.
2. **`IsRootCell.mul_eq_cellProd`.** If `u = 1 + crd p · crd m'`, then
   `Ω(m, t, p) Ω(m', t', p') = Ω(cellProd χ χv m p m' p' t t' u)`. The proof rewrites the
   middle factor `xp(p) xm(m')` with the `mul_eq` field and moves the torus factors
   across the root groups again.
3. **`cellCompatible`.** If `D₁ : IsRootCell i₁ χ χv xp₁ xm₁` and
   `D₂ : IsRootCell i₂ χ χv xp₂ xm₂` (two groups, the same `T`, `χ` and `χv`), then
   `CellGluing.CellCompatible Ω₁ Ω₂`. Given `Ω₁(x) Ω₁(y) = Ω₁(c)`, step 1 gives the unit
   `u` and step 2 gives `Ω₁(x) Ω₁(y) = Ω₁(cellProd …)`. The cell map `Ω₁` is an open
   immersion, hence a monomorphism, so `c = cellProd …`. Step 2 for `D₂` then gives
   `Ω₂(x) Ω₂(y) = Ω₂(c)`.
4. **`exists_iso`.** Let `G₁` and `G₂` be connected reductive. Their structure
   morphisms are smooth, and geometrically integral by the Library's
   `smoothConnectedAffineGeometry`, hence geometrically irreducible.
   `CellGluing.exists_iso_of_cellCompatible`, applied to `Ω₁`, `Ω₂`, the section
   `unitPt T` and step 3 in both directions, gives `ψ : G₁ ≅ G₂` with
   `Ω₁ ≫ ψ = Ω₂`. Precomposing with `torusPt T` gives `i₁ ≫ ψ = i₂`.
5. **`splitRankOneCommonTorusIsomorphism_of_rootCell`.** Take the data of the target
   statement: `G₁`, `G₂`, `T`, `i₁`, `i₂`, `P₁`, `P₂`, `e : J₁ ≃ J₂`, the root and
   coroot matchings, and the rank-one hypothesis for `i₁`.
   - If `J₁` is empty, then `roots i₁ = Set.range P₁.root` is empty, and
     `exists_iso_of_roots_eq_empty` concludes.
   - Otherwise pick `r₁ : J₁`. `roots_eq_of_isRootDatumOf_of_reindex` gives
     `roots i₂ = roots i₁`, which transports the rank-one hypothesis to `i₂`. The
     statement gives root cells `D₁` for `(i₁, P₁, r₁)` and `D₂` for
     `(i₂, P₂, e r₁)`. The matchings `P₂.root (e r₁) = P₁.root r₁` and
     `P₂.coroot (e r₁) = P₁.coroot r₁` put both for the same `χ` and `χv`, and step 4
     concludes.

## Provenance

The reduction is derived, not a formalization of one cited theorem. Conrad, *Reductive
group schemes* (2014), Example 6.2.6 (PDF p.203), proves the Isogeny Theorem in semisimple
rank one. It uses the criterion of Theorem 6.2.4
(SGA 3, Exp. XXIII, 2.3) for maps defined on `T` and on the root groups. This module
takes a different route. By relation (4.2.1) of Conrad's Theorem 4.2.6, a product of two
cell points that lies in the cell has explicit coordinates (`cellProd`). These depend
only on the root and coroot, so two groups with the same torus, root and coroot have the
same multiplication of cell points. The gluing criterion of `OpenCellGluing` then turns
this into an isomorphism.
