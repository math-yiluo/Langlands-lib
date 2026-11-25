# Integral closure over a one-dimensional Noetherian domain

Module `StacksFrontier.RingTheory.IntegralClosure.DedekindDomain`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves a form of Krull–Akizuki for the integral closure of a Noetherian domain in a finite extension of its fraction field.

`IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite` takes a Noetherian domain A of dimension at most one, a fraction field K of A, a finite field extension L of K, and a ring C presenting the integral closure of A in L with compatible algebra maps. It proves that C is a Dedekind domain, contraction from Spec C to Spec A is surjective, and C is quasi-finite over A. In `Algebra.QuasiFinite`, the last conclusion means that each fibre algebra is finite-dimensional over the residue field of its base prime. In particular, the fibres on spectra are finite and the induced residue field extensions are finite.

The proof uses the finiteness of the quotients C/mC for maximal ideals m and propagates it to C/xC for nonzero x of A by multiplying ideals with finitely generated quotients. Each nonzero ideal of C contains such an x from A, so finite generation modulo xC proves Noetherianity. Integral lying over gives surjectivity, and the generic fibre embeds into the corresponding fibre of L.

The dimension bound includes the case where A is a field. The base may fail integral closedness, the field extension may be inseparable, and C may have infinite type over A.

The theorem is Tag 09IG and uses Tag 031F at maximal ideals. The table of references cites EGA 0 23.2.6, EGA 0 23.2.7, EGA 0 23.2.8, EGA IV 18.9.7.8, and EGA IV 9.5.7.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09IG](https://stacks.math.columbia.edu/tag/09IG) | `isDedekindDomain_and_comap_surjective_and_quasiFinite` | Finite fibres and finiteness of the induced residue field extensions are packaged as `Algebra.QuasiFinite A C`, from which they follow by name; `dim A = 1` is weakened to `Ring.DimensionLEOne A`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.2.6 | `isDedekindDomain_and_comap_surjective_and_quasiFinite` | residue extensions |
| EGA | 0 23.2.8 | `isDedekindDomain_and_comap_surjective_and_quasiFinite` | (ii), dim ≤ 1 |
| EGA | 0 23.2.7 | `isDedekindDomain_and_comap_surjective_and_quasiFinite` | partial |
| EGA | IV 18.9.7.8 | `isDedekindDomain_and_comap_surjective_and_quasiFinite` | more general |
| EGA | IV 9.5.7 | `isDedekindDomain_and_comap_surjective_and_quasiFinite` | B is a Dedekind ring |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegralClosure/DedekindDomain.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
