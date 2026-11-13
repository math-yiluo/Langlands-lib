# Transport of smooth residue fibres along base change and open immersions

Author: Worker 9.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4). It shows that the hypothesis "the residue fibre is smooth of relative
dimension `n`" survives two operations: base change of the morphism, and restriction of its
source to an open subscheme.

All declarations are in the namespace `Langlands.GroupScheme.ReducedBaseSmooth`, and all
schemes lie in one universe `u`. For a morphism `f : X ⟶ Y` and `y : Y`,
`f.fiberToSpecResidueField y` is Mathlib's projection of the fibre
`X ×_Y Spec κ(y)` to `Spec κ(y)`.

## Declarations

- `smoothOfRelativeDimension_fiber_of_isPullback`: given a pullback square
  `IsPullback fst snd f g` with `fst : P ⟶ X`, `snd : P ⟶ Y`, `f : X ⟶ Z` and `g : Y ⟶ Z`,
  a point `y : Y` and `n : ℕ`, suppose `f.fiberToSpecResidueField (g y)` is
  `SmoothOfRelativeDimension n`. Then so is `snd.fiberToSpecResidueField y`.
- An instance: for `p : Z ⟶ T`, an open immersion `i : Y ⟶ Z` and `t : T`, the fibre map
  `fiberMap p i t : (i ≫ p).fiber t ⟶ p.fiber t` (defined in `Core.lean`) is an open
  immersion.
- `smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion`: let `j : W ⟶ X` be an open
  immersion, `f : X ⟶ Y`, `y : Y` and `n : ℕ`. If `f.fiberToSpecResidueField y` is
  `SmoothOfRelativeDimension n`, then so is `(j ≫ f).fiberToSpecResidueField y`.

## Provenance

These are standard stability properties of smoothness of fixed relative dimension: stability
under base change and under composition with open immersions. They are stated here as
internal lemmas with derived names.

## Proofs

`smoothOfRelativeDimension_fiber_of_isPullback`. Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback` shows that the residue fibre of `snd` at `y`
is a pullback of the residue fibre of `f` at `g y`, along `Spec κ(y) → Spec κ(g y)`.
`SmoothOfRelativeDimension n` is stable under base change (`MorphismProperty.of_isPullback`).

The instance. `fiberMap p i t` is the map of pullbacks over `Spec κ(t)` induced by the open
immersion `i` and identities. Open immersions are stable under such induced maps
(`MorphismProperty.pullbackMap`).

`smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion`. By
`fiberMap_fiberToSpecResidueField` (from `Core.lean`), the fibre projection of `j ≫ f`
factors as `fiberMap f j y ≫ f.fiberToSpecResidueField y`. The first map is an open
immersion, hence smooth of relative dimension `0`. Mathlib's `smoothOfRelativeDimension_comp`
adds the relative dimensions, giving dimension `0 + n = n`.
