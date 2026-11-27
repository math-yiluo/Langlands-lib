# Differences of lifts into a group scheme

Module `Langlands.AlgebraicGeometry.Deformation.GroupTargetDifference` (namespace
`Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts`).

The module `ElementaryMorphismLifts` measures two lifts `x, y` of the same reduced map into a
smooth target `Z` (a `Target R` over a local ring `R`, with an ideal `I` such that
`maximalIdeal R * I = 0` and `I ≤ maximalIdeal R`) by difference
coordinates `b.difference x y h` (`Target.Coordinates.difference`). This module adds two facts
used for obstruction cochains.

## Targets given by a group scheme

`Target.ofGroup H` is the target with total space `H.X` for a group scheme `H` over `Spec R`, whose
residue group is the base change of `H` to the residue field and whose residue inclusion is the
first projection of that base change. `ofGroup_fibrePoint_mul` shows that the residue point of a
product is the product of the residue points.

For a commutative `H` and a flat test algebra `C`:

- `agree_mul`, `agree_inv`: products and inverses of pairs of lifts that agree modulo `I` agree
  modulo `I`;
- `translatedDifference_mul`: the translated difference of `(x * x', y * y')` is the product of the
  translated differences (via `splitFibrePoint_mul`, `reducePoint_mul`, `constantExtension_mul`);
- `difference_mul`, `difference_inv`, `difference_div`: the difference coordinates are additive,
  `D(x x', y y') = D(x, y) + D(x', y')`, so that `D(x⁻¹, y⁻¹) = -D(x, y)` and
  `D(x x'⁻¹, y y'⁻¹) = D(x, y) - D(x', y')`. Additivity follows from
  `PointChart.linearCoordinates_mul` (module `SplitPointGroupLaw`).

## Post-composition that is the identity on the residue fibre

`translatedDifference_comp_eq`: for two maps `F₁ F₂ : W ⟶ Z.X` that agree on the actual residue
fibre of `W` (`pullback.fst W.hom r ≫ F₁ = pullback.fst W.hom r ≫ F₂`), the translated differences
of `x ≫ F₁, y ≫ F₁` and `x ≫ F₂, y ≫ F₂` are equal. The split test of the two lifts lies over the
residue field (`splitPoint_over`), so `comp_eq_of_fibre` applies to it.

## Provenance

The difference of two lifts is the torsor structure of SGA 1, Exposé III, Proposition 5.1 and
Corollaire 5.2 (recomposed edition, arXiv math/0206203v2, printed pp. 59–61). For a group target
the additivity of differences is the compatibility of that torsor structure with the group law,
which this module proves from the coordinate description of differences.
