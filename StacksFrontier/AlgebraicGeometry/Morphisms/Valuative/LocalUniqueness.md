# Local uniqueness from equality on stalks

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalUniqueness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two morphisms over a base that agree at a point and on its local ring agree near that point under a hypothesis of local finite type on the target or a germ injectivity condition on the source.

`AlgebraicGeometry.exists_open_eq_of_stalkMap_eq` considers `S`-morphisms `f, g : X ⟶ Y` taking `x ∈ X` to the same `y ∈ Y`, with `x` and `y` over the same point of `S`. The hypothesis compares the two stalk maps after transport along the equality of the image points. The conclusion gives an open `U` containing `x` on which the restrictions of `f` and `g` are equal.

The theorem accepts any one of four hypotheses. The target structure map is locally of finite type, the source is integral, the source is locally Noetherian, or the source is reduced with finitely many irreducible components. For the finite type case the proof chooses compatible affine charts and clears the localization denominators on a finite set of algebra generators. This gives equality on one basic open. The three source conditions yield germ injectivity, so those branches use Mathlib’s `spread_out_unique_of_isGermInjective`.

The statement gives the local uniqueness assertion of Tag 0BX6. It also references EGA I 6.5.1 (i).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BX6](https://stacks.math.columbia.edu/tag/0BX6) | `exists_open_eq_of_stalkMap_eq` | local_uniqueness |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 6.5.1 | `exists_open_eq_of_stalkMap_eq` | (i) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Valuative/LocalUniqueness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
