# Depth under localization

Module `StacksFrontier.RingTheory.Depth.Localization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file bounds how much depth can drop on localizing at a prime.

`Module.depth_le_depth_localized_add_ringKrullDim_quotient` assumes a finite module M over a Noetherian local ring R and a prime p of R. The maximal-ideal depth of M is at most the depth of M localized at p over R localized at p, plus dim(R/p). It restates `Stacks.Depth.LocalizedCoheightBound.solution`.

In the proof dim(R/p) is the coheight of p. If a natural lower bound on depth exceeds that coheight, the associated prime dimension bound ensures that no associated prime contains p. Prime avoidance and quotienting by a nonzerodivisor in p construct a weakly regular sequence whose length plus the coheight reaches the bound. Localization preserves that sequence. The two steps that use depth directly, that quotienting by a nonzerodivisor lowers a depth bound by one and that a localized weakly regular sequence bounds the localized depth, are private lemmas in the namespace `Stacks.Depth.LocalizedInfimum`.

The result accepts abstract localizations specified by `IsLocalization.AtPrime` and `IsLocalizedModule`. It compares values in `WithBot ℕ∞` and includes the case of a zero localized module, with infinite depth. Depth is the library’s `Module.stacksDepth` (Tag 00LI), which the docstrings and the note of the tag call `Module.depth`. The first two module docstrings announce the formula of Tag 0AUK for depth over a finite extension, which the file does not contain.

References include Tag 0FCC.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0FCC](https://stacks.math.columbia.edu/tag/0FCC) | `depth_le_depth_localized_add_ringKrullDim_quotient` | Stated in `WithBot ℕ∞` with the smaller side on the left, for `Module.depth` (Tag 00LI) along the maximal ideals of `R` and of `Rₚ`, and with the localizations presented by `IsLocalization.AtPrime` and `IsLocalizedModule`. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/Localization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 19 declarations of the source file 7 are kept. The 12 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 2 references to EGA and SGA that the source writes as attributes of that library belong to a declaration left out; none is in the file.
