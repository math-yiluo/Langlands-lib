# Smoothness at a prime under base change

Module `StacksFrontier.RingTheory.Smooth.LocusBaseChangeAtPrime`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Smoothness of a finitely presented algebra at a prime survives arbitrary base change. It can also be recovered from the new algebra at a prime above it when one of the two maps out of the original base is flat.

- `Algebra.isSmoothAt_of_isSmoothAt_of_isPushout` takes R → A of finite presentation, a base change A′ along R → R′, and a prime q′ of A′ over q of A. Smoothness of A over R at q implies smoothness of A′ over R′ at q′.
- `Algebra.isSmoothAt_iff_isSmoothAt_fiber` takes R → A flat and finitely presented and q lying over p. For a fibre prime Q contracting to q under the canonical map A → κ(p) ⊗ A over R, smoothness at q is equivalent to smoothness of the fibre over κ(p) at Q.
- `Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat` gives the equivalence between smoothness at q and at q′ under the additional hypothesis `hflat`, which requires R → A or R → R′ to be flat.

Ascent base-changes a smooth principal neighbourhood. For the reverse implication, flatness of R′ over R allows evaluation of the flat smooth-locus equality. Flatness of A over R instead allows the fibre criterion on both sides, since the second fibre is the base change of the first along the corresponding residue field extension.

Smoothness is Mathlib’s `Algebra.IsSmoothAt`. The base change statements accept an abstract pushout with primes related by contraction. The fibre criterion is the ring form of conditions (1) and (2) of Tag 01V9, with flatness part of the hypotheses.

## References

Tag 00TF gives smoothness from a smooth fibre, Tag 00TG gives the smooth locus under flat base change, and Tag 02UQ gives the residue field comparison. Tag 02V4 is the corresponding scheme result. The EGA and SGA references are EGA IV 17.7.2 and SGA 3 VIB 3.10.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 3.10 | `isSmoothAt_iff_isSmoothAt_fiber` | special case |
| EGA | IV 17.7.2 | `isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat` | (ii), affine case |
| SGA | 3 VIB 3.10 | `isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Smooth/LocusBaseChangeAtPrime.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
