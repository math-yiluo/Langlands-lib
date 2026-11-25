# Flatness at a quasi-finite point over a polynomial ring

Module `StacksFrontier.RingTheory.CohenMacaulay.Locus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a map from a polynomial ring to a finite-type algebra over a field, flatness at a quasi-finite point is determined by Cohen–Macaulayness and a relative dimension condition.

## Main result

`Module.Flat.atPrime_iff_isMaximalCohenMacaulay_and_relativeDimensionAt_eq` takes a field k, a finite-type k-algebra S, and a k-algebra map from a polynomial ring in d variables to S that is quasi-finite at a prime q of S. The local ring S_q is flat over the polynomial ring exactly when S_q is Cohen–Macaulay and `Algebra.relativeDimensionAt k q` equals d.

Write p for the contraction of q. Quasi-finiteness gives height(q) ≤ height(p) and a zero-dimensional closed fiber for the localized map. The forward implication uses Cohen–Macaulay ascent from the regular local ring at p, and the reverse uses miracle flatness when the heights agree. To connect equal heights with the dimension condition, the proof writes relative dimension as height plus residue-field transcendence degree and uses the finiteness of κ(q) over κ(p).

The equivalence is pointwise and assumes `Algebra.QuasiFiniteAt` at q. For a globally quasi-finite map it gives the equality of loci on the whole spectrum. The polynomial ring is `MvPolynomial σ k` for a finite index type σ, with d given by `Nat.card σ`. The relative dimension is taken over k, and the theorem allows any model of the localization S_q.

## References

Tag 00RE is the flatness criterion, and Tag 00QD defines relative dimension. The proof uses Tag 00QF for the height bound, Tag 00P1 for the dimension formula, Tag 00R5 for ascent, and Tag 00R4 for miracle flatness.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00RE](https://stacks.math.columbia.edu/tag/00RE) | `Module.Flat.atPrime_iff_isMaximalCohenMacaulay_and_relativeDimensionAt_eq` | Cohen-Macaulayness of the Noetherian local ring `S_𝔮` (Definition 00N8) is `Module.IsMaximalCohenMacaulay Sq Sq`; `k[y_1, …, y_d]` is `MvPolynomial σ k` with `d = Nat.card σ`; the localization is an abstract `IsLocalization.AtPrime`; and the equality of subsets of `Spec S` is stated pointwise at `𝔮`, with the source's global quasi-finiteness of `φ` weakened to quasi-finiteness at `𝔮` (Definition 00PL). See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/Locus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
