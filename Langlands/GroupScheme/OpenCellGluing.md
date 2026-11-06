# Isomorphisms of group schemes from compatible open cells

Author: Worker 1388.

Module `Langlands.GroupScheme.OpenCellGluing`, namespace
`Langlands.GroupScheme.CellGluing`. This is an internal helper module. It proves a
general gluing criterion: two group schemes are isomorphic once they share an open cell
on which the multiplication relations agree.

## Main result

`exists_iso_of_cellCompatible`: let `S` be a scheme and `G`, `H` group schemes over `S`
whose structure morphisms are smooth and geometrically irreducible. Assume:

- `j : C ⟶ G.X` and `ν : C ⟶ H.X` are morphisms over `S` from a common `C : Over S`,
  and both underlying morphisms of schemes are open immersions;
- `e : 𝟙_ (Over S) ⟶ C` is a section with `e ≫ j = 1` and `e ≫ ν = 1`;
- `CellCompatible j ν` and `CellCompatible ν j` hold.

Then there is an isomorphism `ψ : G ≅ H` of group schemes with `j ≫ ψ.hom.hom.hom = ν`.

`CellCompatible j ν` says: for every `Z : Over S` and all points `x y c : Z ⟶ C`,
`(x ≫ j) * (y ≫ j) = c ≫ j` implies `(x ≫ ν) * (y ≫ ν) = c ≫ ν`. In words, every
multiplication relation between cell points that holds in `G` also holds in `H`. The
theorem uses this condition in both directions.

Two further results are used on their own:

- `hom_ext_cell`: two homomorphisms `f f' : G ⟶ K` with `j ≫ f.hom.hom = j ≫ f'.hom.hom`
  are equal. Here `G` is smooth with geometrically irreducible fibres, `j` is an open
  immersion and some point of `C` maps to `1`.
- `glueHom hc e he : G ⟶ H` is a homomorphism with `j ≫ (glueHom hc e he).hom.hom = ν`
  (`cell_comp_glueHom`). It needs only `CellCompatible j ν` and the hypotheses on `G`.

## The implemented proof

Points are morphisms `Z ⟶ G.X` in `Over S`, which form a group.

1. **Cell points.** `InCell j x` says that the image of `x` lies in the image of `j`.
   Such a point has a unique cell coordinate `coord x hx : Z ⟶ C` with
   `coord x hx ≫ j = x`. This is the Library's `OpenCell.lift`, and uniqueness holds
   because `j` is a monomorphism. Next, `cellMap j ν x` is `coord x hx ≫ ν` for a cell
   point `x`; on other points it is the junk value `1`, which no lemma uses.
   `CellCompatible` gives `cellMap_mul`: `φ(xy) = φ(x) φ(y)` whenever `x`, `y` and `xy`
   are cell points. From this follow `cellMap_one` and `cellMap_inv`.
2. **Auxiliary-point covers.** For a point `y : Z ⟶ G.X`, the proof works on opens `V`
   of `Z ⊗ G.X`, where the second factor is an auxiliary point `g`. The open `V`
   *covers* `Z` (`Covers`) when its projection to `Z` is surjective. A section
   `s : Z ⟶ Z ⊗ G.X` that lands in `V` makes `V` cover (`covers_of_section`). Two
   covering opens meet in a covering open (`Covers.inf`): this is the Library's
   `OpenCell.surjective_intersection` applied to the smooth, geometrically irreducible
   projection `Z ⊗ G.X ⟶ Z`. A covering open gives a smooth surjective morphism to `Z`,
   hence an effective epimorphism (`Covers.effectiveEpi`, Mathlib's fpqc instance) and an
   epimorphism in `Over S` (`Covers.epi`). The open where a given expression in `y` and
   `g` lies in the cell is `cellOpen`. It covers as soon as one choice of `g` (`1`, `y⁻¹`,
   `h⁻¹`, …) puts the expression in the cell, because `e` maps to `1`.
3. **Splitting a point.** `splitOpen j y` is the open where `g` and `y g⁻¹` are cell
   points. It covers because of the sections `g = 1` and `g = y`
   (`covers_splitOpen`). So, after an fppf cover, every point is a product of two cell
   points. This already proves `hom_ext_cell`.
4. **Independence.** `cellMap_split` shows `φ(y h⁻¹) φ(h) = φ(y g) φ(g)⁻¹` whenever
   `h`, `g`, `hg`, `y h⁻¹` and `y g` are cell points. Next, `cellMap_indep` proves
   `φ(y h⁻¹) φ(h) = φ(y h'⁻¹) φ(h')` for any two cell splittings. It applies
   `cellMap_split` twice, after passing to an open with four cell conditions on the
   auxiliary `g`: `g`, `hg`, `h'g` and `yg`. That open covers because of the sections
   `1`, `h⁻¹`, `h'⁻¹` and `y⁻¹`.
5. **Descent.** On the universal split open `univOpen j` of `G.X ⊗ G.X` (the case
   `y = 𝟙 G.X`), `univMap` is the morphism `(y, g) ↦ φ(y g⁻¹) φ(g)`. By step 4 it equalizes
   the two pullbacks along the projection to `G.X` (`univMap_cond`). Effective descent
   along that projection gives `glue : G.X ⟶ H.X` (`glueLeft`, `glue`).
6. **Properties of `glue`.** For every cell splitting,
   `y ≫ glue = φ(y h⁻¹) φ(h)` (`comp_glue`). Hence `glue` sends `1` to `1`
   (`glue_one`) and restricts to `ν` on the cell (`cell_comp_glue`). It also satisfies
   `(y x) ≫ glue = (y ≫ glue) φ(x)` for cell points `x` (`glue_mul_cell`, on an open with
   conditions `g`, `y g⁻¹`, `g x`). Splitting `y'` then gives multiplicativity on all
   points (`glue_mul`).
7. **Homomorphism and inverse.** `glueHom` is `glue` made into a homomorphism by the
   Library's `homOfPoints`. By symmetry there is also `glueHom hc' e he' : H ⟶ G`. Both
   composites restrict to `j` (respectively `ν`) on the cell, so `hom_ext_cell` makes them
   the identities.

## Provenance

The module is derived, not a formalization of one cited theorem. The idea of extending a
map from an open dense cell, multiplicative where defined, to a homomorphism goes back to
Weil's theorem on group chunks, which Conrad's notes *Reductive group schemes* (2014,
Theorem 6.2.4 and Example 6.2.6) use for isomorphisms of rank-one groups. The
implementation here is different. There is no density or rational-map argument. Every
identity is checked after pulling back along a smooth surjective open of `Z ⊗ G.X` cut out
by cell conditions on an auxiliary point. Such an open covers because one explicit section
lands in it, and two covering opens meet in a covering open because the fibres are
geometrically irreducible. The pattern follows the Library's `OpenCell.kernelι_eq_zero`
and the descent in `HomDescent`.
