# Ascent of normality along smooth morphisms

Module `StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that the source of a smooth morphism with normal target is normal, together with helpers on normality of affine schemes and on open covers.

## Main results

- `isNormal_of_smooth`: if `f : X ⟶ Y` is smooth and `Y` is normal, then `X` is normal. `isNormal_of_smooth_of_isAffine` is the case of `Y` affine.
- `isNormalRing_appTop_of_isNormal` and `isNormal_of_isNormalRing_appTop`: an affine scheme `X` is normal if and only if `Γ(X, ⊤)` is a normal ring, one direction each.
- `IsNormal.of_openCover`: a scheme with an open cover by normal schemes is normal.

The three helpers are read off the library's `isNormal_tfae`, whose own helpers are private. All declarations are in the namespace `AlgebraicGeometry`.

## Proofs

For `Y` affine, the ring of global sections of each member of the affine cover of `X` is a smooth algebra over the normal ring `Γ(Y, ⊤)`, hence normal by `Algebra.isNormalRing_of_smooth` (the ring statement of Tag 033C), and normality is local on the cover. In general, `f` is base changed along an affine open cover of `Y`, which gives an open cover of `X`.

## Watch for

- Normality is the library's `IsNormal`: every local ring is an integrally closed domain.
- `isNormal_of_smooth` carries no tag; the comments assign Tag 033C to the ring statement it uses.
- The module docstring presents the file as proving that normality is local in the étale topology (Tag 034F), with descent along flat morphisms and the étale case. The file holds only the ascent half above; its sections on descent and on Tag 034F are empty.

## References

Tag 033C, for the ring statement used; the module docstring cites further tags for results the file does not hold. The table below lists places in SGA 3.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 X 8.4 | `isNormal_of_smooth_of_isAffine` | special case |
| SGA | 3 X 8.9 | `isNormal_of_smooth` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Descent/EtaleLocal/Normal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 5 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isClosedUnderIsomorphisms_isNormal`, `AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`, `AlgebraicGeometry.isNormal_of_etale`, `AlgebraicGeometry.isNormal_of_forall_exists_flat`, `isDomain_and_isIntegrallyClosed_of_faithfullyFlat`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
