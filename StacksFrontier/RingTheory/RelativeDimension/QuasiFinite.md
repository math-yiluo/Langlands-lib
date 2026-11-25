# Quasi-finite maps to affine space from relative dimension

Module `StacksFrontier.RingTheory.RelativeDimension.QuasiFinite`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A finite-type commutative R-algebra S of relative dimension n at a prime q admits, on a principal neighbourhood of q, a quasi-finite map of spectra to affine n-space over R.

`quasiFinite_over_polynomial_of_relativeDimension` takes a prime p of R, a point `qbar` of the fibre spectrum over p, and `hqbar`, identifying its contraction with q. If the relative dimension at `qbar` equals the natural number n, the theorem produces g outside q and a ring map φ from `MvPolynomial (Fin n) R` to `Localization.Away g`. The map commutes with the structure maps from R and is finite type and quasi-finite on the whole localization.

`fiberMap` is the map from S to the fibre ring, sending s to 1 ⊗ s. The file defines `krullDimAt` as the infimum of the Krull dimensions of open neighbourhoods and proves agreement with `stacksTopologicalKrullDimAt` via `krullDimAt_eq_topologicalKrullDimAt`. Its own `relativeDimensionAt` applies this to an explicit prime of the fibre ring.

The proof first finds a principal neighbourhood with fibre of dimension n, applies Noether normalization there using dimension invariance under finite injective maps, and clears denominators to lift the n coordinates. Finiteness after residue-field base change gives weak quasi-finiteness at the chosen point, and Zariski’s main property supplies a second principal neighbourhood on which the map is quasi-finite, with the two localizations combined into the single localization in the conclusion.

## References

Stacks Project Tag 00QE for the main result, Tag 00QD and Tag 0055 for the dimension definitions, Tag 00OW and Tag 00OK for normalization and dimension, and Tag 00PM, Tag 00PN, Tag 00QA and Tag 00Q9 for the quasi-finite steps. EGA 0, 14.1.2, for dimension at a point. EGA IV, 17.10.1, and SGA 3, XI, 1.9, for relative dimension. EGA II, 6.2.1 (b) ⇒ (a), and EGA IV, 13.1.4, for shrinking to the quasi-finite locus.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00QE](https://stacks.math.columbia.edu/tag/00QE) | `quasiFinite_over_polynomial_of_relativeDimension` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 14.1.2 | `krullDimAt` |  |
| SGA | 1 II 5.9 | `krullDimAt` |  |
| SGA | 3 VIB 1.5 | `krullDimAt` |  |
| SGA | 7 XV 1.2 | `krullDimAt` |  |
| EGA | IV 9.4.1 | `fiberMap` | special case |
| EGA | IV 17.10.1 | `relativeDimensionAt` | affine case |
| SGA | 3 XI 1.9 | `relativeDimensionAt` | special case |
| EGA | 0 16.1.5 | `ringKrullDim_eq_of_finite_injective` | special case |
| EGA | IV 5.4.3 | `ringKrullDim_eq_of_finite_injective` | more general |
| EGA | II 6.2.1 | `exists_quasiFinite_localization_of_wqf` | (b) ⇒ (a), affine case |
| EGA | IV 13.1.4 | `exists_quasiFinite_localization_of_wqf` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RelativeDimension/QuasiFinite.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 11 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
