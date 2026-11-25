# Flat integral closures over Dedekind domains

Module `StacksFrontier.RingTheory.DedekindDomain.IntegralClosureFlat`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a Dedekind domain, K its fraction field, L an extension field of K, and B an integral closure of A in L. The file proves flatness of B over A and gives a finiteness condition for universal openness of the corresponding spectrum map.

`IsIntegralClosure.flat` proves flatness, with `integralClosure.flat` specializing to the concrete integral closure. If B is finite as an A-module, `IsIntegralClosure.universallyOpen_specMap_algebraMap` proves that Spec B ⟶ Spec A is universally open.

B is torsion-free because it embeds in L, and torsion-free modules over Dedekind domains are flat. For finite B, Noetherianity gives finite presentation, so the flat spectrum map is universally open.

The scheme statement places A and B in the same universe. The module docstring also announces that every base change of Spec B ⟶ Spec A is an open map; that result is not in this file. The flatness result is a special case of EGA 0 6.3.4. The file also cites Tag 0AUW and Tag 01UA.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 6.3.4 | `IsIntegralClosure.flat` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DedekindDomain/IntegralClosureFlat.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `IsIntegralClosure.isOpenMap_of_isPullback`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
