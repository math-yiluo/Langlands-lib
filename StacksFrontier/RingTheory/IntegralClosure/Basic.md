# Integral closure in finite products of ring maps

Module `StacksFrontier.RingTheory.IntegralClosure.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file shows that integral closure commutes with finite products of ring maps.

## Main results

- `IsIntegralClosure.pi_iff` takes a finite family of maps Rᵢ → Sᵢ of commutative rings and candidate closure maps S′ᵢ → Sᵢ. The product of the S′ᵢ is an integral closure of the product of the Rᵢ in the product of the Sᵢ exactly when each S′ᵢ is an integral closure of Rᵢ in Sᵢ. Taking S′ = R, the product map is integrally closed exactly when each Rᵢ → Sᵢ is.

The proof uses coordinatewise integrality in products, `isIntegral_pi_iff` of `StacksFrontier.RingTheory.IntegralClosure.Pi`. For the direction from the product to the factors, the product statement is tested on elements supported at one index (`Pi.single`); private lemmas read off injectivity of the structure map, membership in its range and integrality of such elements coordinate by coordinate.

## Scope and references

The comparison is stated for a finite index type, using `IsIntegralClosure` to express injectivity and the range of the closure map. The result is Tag 0CY9.

Comments in the file name the Mathlib theorems that now carry Tags 00PQ, 02JJ, 02JK, 02JM and 00GN; the tables list them, with the references to EGA and SGA attached to them. The module docstrings of the file also describe a finite-presentation criterion (Tag 0564), the transitivity of integral closure and a scaling lemma for integrality (Tag 00PV); none of these is in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CY9](https://stacks.math.columbia.edu/tag/0CY9) | `IsIntegralClosure.pi_iff` |  |
| [00PQ](https://stacks.math.columbia.edu/tag/00PQ) | `RingHom.isIntegralElem_leadingCoeff_mul` | scaling by the leading coefficient makes an element integral |
| [00PQ](https://stacks.math.columbia.edu/tag/00PQ) | `RingHom.isIntegralElem_zero` | the degenerate case, where the top coefficient vanishes |
| [02JJ](https://stacks.math.columbia.edu/tag/02JJ) | `Algebra.finite_iff_isIntegral_and_finiteType` | finite = integral + finite type |
| [02JK](https://stacks.math.columbia.edu/tag/02JK) | `Algebra.IsIntegral.tensorProduct` | (1) |
| [02JK](https://stacks.math.columbia.edu/tag/02JK) | `Module.Finite.base_change` | (2) |
| [02JM](https://stacks.math.columbia.edu/tag/02JM) | `RingHom.IsIntegral.tower_top` | (1) |
| [02JM](https://stacks.math.columbia.edu/tag/02JM) | `RingHom.Finite.of_comp_finite` | (2) |
| [00GN](https://stacks.math.columbia.edu/tag/00GN) | `RingHom.IsIntegral.trans` | integrality is stable under composition |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.0.5 | `Algebra.finite_iff_isIntegral_and_finiteType` |  |
| EGA | II 6.1.2 | `Algebra.finite_iff_isIntegral_and_finiteType` | more general |
| EGA | II 6.1.5 | `Algebra.IsIntegral.tensorProduct` | (iii), integral, affine |
| SGA | 1 III 1.4 | `Module.Finite.base_change` | partial |
| EGA | III 2.6.2.1 | `Module.Finite.base_change` | special case |
| EGA | II 6.1.5 | `Module.Finite.base_change` | (iii), finite, affine |
| EGA | II 6.1.5 | `RingHom.IsIntegral.tower_top` | (v), special case |
| EGA | II 6.1.5 | `RingHom.IsIntegral.trans` | (ii), integral, affine |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegralClosure/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 22 declarations of the source file 6 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 8 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
