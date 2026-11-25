# Freeness of syzygies at a point of flatness

Module `StacksFrontier.RingTheory.Flat.SyzygyFreeLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that, at a prime where the resolved module is flat over the base, a syzygy of a finite free resolution becomes free after localizing, provided the fibre ring there is regular local of small dimension.

## Main results

- `Module.free_localizedModule_atPrime_of_forall_shortExact` proves the stalk result for a flat algebra P over R, both Noetherian, from short exact sequences 0 → Kᵢ₊₁ → Fᵢ → Kᵢ → 0 with Fᵢ finite free and Kₙ finite. It assumes that K₀ localized at 𝔮 is R-flat and that P_𝔮/𝔭P_𝔮 is regular local of dimension at most n, with 𝔭 the contraction of 𝔮, and concludes that Kₙ localized at 𝔮 is free over P_𝔮.
- `Ideal.localizationFiberPointRingEquiv` identifies that quotient with the local ring of the fibre over 𝔭 at the point corresponding to 𝔮. For a polynomial ring P = R[x₁, …, xₙ], `Ideal.isRegularLocalRing_fiberRing_mvPolynomial` and `Ideal.ringKrullDim_fiberRing_mvPolynomial_le` prove regularity and the dimension bound n for this local ring.

`Module.Flat.of_forall_shortExact` propagates flatness up the sequences, allowing them to stay exact on the fibre. There `IsRegularLocalRing.free_of_forall_shortExact` uses the global dimension bound to show that a finite n-th syzygy in such sequences with projective middle terms is free. The local flatness criterion lifts a free fibre to the stalk. Along the way, `LinearMap.injective_baseChange_quotient_iff` reads injectivity on the fibre over the base ring, and `Module.Free.of_isLocalizedModule` says that a localization of a free module is free.

## Scope and references

The stalk theorem gives the syzygy step in the proof of openness of the flat locus. It places R, P and the modules in one universe. The module docstring also announces a finite free resolution over R[x₁, …, xₙ] whose n-th syzygy is free on a basic open neighbourhood, and lemmas on finitely generated submodules and their localizations; these are not in this file. Stacks Project, Tag 00HM, Tag 00LP, Tag 00MH and Tag 00RC. EGA 0 1.0.4 and EGA IV 2.1.10.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.0.4 | `Ideal.mem_map_smul_top_iff_mem_smul_top` | JM = (BJ)M |
| EGA | IV 2.1.10 | `Module.Flat.of_forall_shortExact` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/SyzygyFreeLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 19 declarations of the source file 11 are kept. The 8 left out are not needed by the results for which the extract is made: `Module.eq_zero_of_forall_exists_smul_eq_zero_of_flat`, `Module.exists_away_free_syzygy_of_flat_atPrime_mvPolynomial`, `Module.flat_localizations_injective`, `Submodule.exists_fg_le_forall_localized_eq`, `Submodule.exists_fg_le_localized_eq`, `Submodule.exists_smul_mem_of_localized_le`, `Submodule.fg_localized_ker`, `Submodule.localized_liftQ_injective`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
