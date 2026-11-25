# Local dimension under quasi-finite maps

Module `StacksFrontier.RingTheory.QuasiFinite.Dimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

At a quasi-finite point, a map of affine spectra bounds the dimension of the source local ring by that of the target local ring. The file expresses the comparison entirely in terms of prime heights.

`Ideal.height_le_height_of_liesOver_of_quasiFiniteAt`, also stated as `Stacks.QuasiFinite.HeightBound.solution`, takes prime ideals 𝔮 of a commutative R-algebra S and 𝔭 of R, with 𝔮 lying over 𝔭. If `Algebra.QuasiFiniteAt R 𝔮` holds, then 𝔮 has height at most that of 𝔭. These heights give the Krull dimensions of any models of the corresponding localizations by `IsLocalization.AtPrime.ringKrullDim_eq_height`.

Quasi-finiteness at 𝔮 passes to every prime below it by `Algebra.QuasiFiniteAt.of_le`. By `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`, comparable primes there with the same contraction coincide. Thus contraction carries chains below 𝔮 to chains of the same length below 𝔭. The order lemmas justify computing height within that lower interval.

The Lean theorem allows arbitrary commutative R-algebras. For finite-type algebras, `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber` connects the hypothesis to the isolated-point formulation in the Stacks Project.

Stacks Project, Tag 00QF, with Tag 00PL and Tag 00PK for the quasi-finite condition. The discussion of the Stacks Project proof cites Tag 00OM, Tag 00Q9, and Tag 00OJ.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00QF](https://stacks.math.columbia.edu/tag/00QF) | `Ideal.height_le_height_of_liesOver_of_quasiFiniteAt` | `dim(S_𝔮)` and `dim(R_𝔭)` are `𝔮.height` and `𝔭.height`, model-independently by `IsLocalization.AtPrime.ringKrullDim_eq_height`; quasi-finiteness at `𝔮` (Definition 00PL) is `Algebra.QuasiFiniteAt R 𝔮`, which the source's finite type hypothesis identifies with the source's notion by `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, and which the conclusion needs without it. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/QuasiFinite/Dimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
