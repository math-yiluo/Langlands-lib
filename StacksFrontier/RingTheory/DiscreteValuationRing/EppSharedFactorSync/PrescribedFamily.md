# Prime-degree solvers over a perfect residue field

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.PrescribedFamily`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file states the prime-degree solver obligations for towers of complete discrete valuation rings over a perfect residue field, reduces them to the wild Galois case, and passes from one tower to finite families. All rings and fields lie in one universe.

- `isWeaklyUnramified_of_finrank_eq_one`: in a tower A → B → C, with L and M the fraction fields of B and C, B complete, A → B weakly unramified and [M : L] = 1, the map A → C is weakly unramified. C is module-finite over B by the private `module_finite_of_isAdicComplete_of_finite_fractionRing`, so the ramification index of B → C divides [M : L].
- `PrimeDegreeSolvable p` asks for a finite solution field when M/L is finite and either purely inseparable of degree p or Galois of prime degree, with A and B complete, A → B weakly unramified, Epp’s condition on A → B and perfect base residue field of characteristic p. `WildPrimeDegreeSolvable p` is the same obligation for M/L Galois of degree exactly p.
- `primeDegreeSolvable_of_wildPrimeDegreeSolvable` discharges the purely inseparable and tame cases given `hwild : WildPrimeDegreeSolvable p` for the Galois degree-p case. For a Galois layer of prime degree other than p, the ramification index of A → C equals that of B → C, which divides the degree and so is prime to p; the residue extension is separable because the base residue field is perfect.
- `FamilyPrimeDegreeSolvable p` asks, for a finite family of such towers A → Bᵢ → Cᵢ over one base A, for one finite K₂/K over which every A → Cᵢ has a weak solution. `familyPrimeDegreeSolvable_of_primeDegreeSolvable` derives it from the one-member solver `hsingle`: the separate solution fields embed in a common finite overfield, where the weak solutions persist over a perfect residue field.

The module docstring and two long section comments describe a descent along a prescribed extension and the degree-one base case of `FamilyTowerSolvable`, which the file does not contain; the section that the first comment introduces is empty.

The docstring of `isWeaklyUnramified_of_finrank_eq_one` cites Tag 09F8; Tags 09ES, 09ET and 09F9 occur only in the comment on the prescribed-extension descent.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFactorSync/PrescribedFamily.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 49 declarations of the source file 7 are kept. The 42 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
