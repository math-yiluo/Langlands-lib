# Nowhere density in fibres near the generic point

Module `StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseGenericFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite type morphism of schemes over an irreducible base, nowhere density of a closed subset in the generic fibre persists over a nonempty open of the base.

## Main results

- `AlgebraicGeometry.exists_open_isNowhereDense_fiber` takes a quasi-compact, locally finite type morphism `f : X ⟶ Y`, an irreducible `Y`, an explicit generic point `η` of `Y`, and a closed subset `Z` of `X`. If the preimage of `Z` under `f.fiberι η` is nowhere dense, there is a nonempty open in `Y` over which the preimage is nowhere dense in every fibre.
- `AlgebraicGeometry.exists_open_isNowhereDense_fiber_of_isReduced` gives the same conclusion for a reduced base, with the generic-point hypothesis supplying the irreducibility used in the proof.
- Five lemmas on `AlgebraicGeometry.Scheme.Hom.asFiberAt` (imported from `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourcePoint`), the point of a fibre given by a point of the source and an arbitrary proof that it lies over the base point, such as `Scheme.Hom.fiberPt_congr` and `Scheme.Hom.fiberι_fiberPt`, let the proof compare fibres over equal points.

The proof passes to the reduction of the base by a universal homeomorphism. Over the reduced base, generic flatness gives a common open on which the source and the reduced closed subscheme supported on `Z` are flat and finitely presented. If a fibre of that subscheme over this open contains an ambient component's generic point, flatness lifts the point to the generic fibre. Fibre dimension along specialization then forces the closed subset in the generic fibre to contain an ambient component, contradicting nowhere density.

The schemes share one universe, and the finite type hypotheses are split between `LocallyOfFiniteType` and `QuasiCompact`. The file ends with two section comments, on guard statements showing that the generic-fibre hypothesis is needed and on the form used for Tag 0559; the sections are empty, and the statements they announce are not in this file.

## References

Stacks Project Tag 054X, with reduction, generic flatness and fibre dimension from Tag 054M, Tag 052B and Tag 054U.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [054X](https://stacks.math.columbia.edu/tag/054X) | `exists_open_isNowhereDense_fiber` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/GeometricallyIntegral/NowhereDenseGenericFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 9 are kept. The 5 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.dense_fiberι_preimage_iff_isNowhereDense_compl`, `AlgebraicGeometry.exists_open_dense_fiber_of_isOpen`, `AlgebraicGeometry.isNowhereDense_fiberι_preimage_empty`, `AlgebraicGeometry.not_exists_open_isNowhereDense_fiber_univ`, `AlgebraicGeometry.not_isNowhereDense_fiberι_preimage_univ`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
