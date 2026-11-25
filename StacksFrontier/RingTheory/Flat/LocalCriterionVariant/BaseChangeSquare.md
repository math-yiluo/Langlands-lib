# Flatness after base change and localization

Module `StacksFrontier.RingTheory.Flat.LocalCriterionVariant.BaseChangeSquare`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves a flatness criterion for a square of commutative rings in which S′ is a localization of S ⊗ᵣ R′. It uses the map on Tor associated to an ideal of R and its extension to R′, and allows a larger ideal in the target.

Let M be finite over S and let f : M → M′ exhibit base change to S′. Both criteria assume R′ and S′ are Noetherian local rings, the map R′ → S′ is local, and the square and module actions are compatible. In particular, `hR'` identifies the given R′ → S′ with the composite through S ⊗ᵣ R′.

- `Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero` assumes also that R is local, R → R′ is local, and I is a proper ideal of R. If M/IM is flat over R/I and the canonical Tor₁ map for I and IR′ is zero, then M′ is flat over R′.
- `Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero_of_mem` uses any proper ideal J of R′ containing IR′. It gives the same conclusion from flatness of M/IM over R/I, flatness of M′/JM′ over R′/J, and zero Tor₁ map for I and J.

The proof clears denominators and applies the kernel description `Stacks.Flat.LocalCriterion.key` to obtain injectivity of J ⊗ M′ → R′ ⊗ M′ over R′. It then uses the Noetherian local flatness criterion. For J = IR′, quotient flatness passes by base change and then localization via `Stacks.Flat.LocalCriterion.flat_quotient_of_isLocalizedModule`. The tensor helpers transport injectivity through localization and re-association of base change.

The hypothesis `htor` is given as a kernel inclusion. The canonical tensor map taking a ⊗ x to a ⊗ f(x) must vanish on the kernel of I ⊗ᵣ M → R ⊗ᵣ M. The larger-ideal version explicitly assumes target quotient flatness in `hflatJ` and uses properness of J in place of locality of R → R′.

## References

Tag 00MO is the extension-ideal criterion. The proof uses Tag 00ML and the tensor form of Tor in Tag 00M6, with the comparisons associated to Tag 00MM, Tag 00MN and Tag 00HI. The larger ideal appears in the proof of Tag 0471. Related references are EGA IV 11.2.5 (case b for local rings) and IV 11.3.12 (partial).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00MO](https://stacks.math.columbia.edu/tag/00MO) | `of_flat_quotient_of_tor_one_map_eq_zero` | `Tor₁` is spelled through Remark 00M6 as `Ker(I ⊗_R M → R ⊗_R M)`, and the hypothesis that `Tor_1^R(M, R/I) → Tor_1^{R'}(M', R'/I')` is zero as the vanishing on that kernel of the canonical map `I ⊗_R M → I' ⊗_{R'} M'`. `M'` and `S'` are abstract (`IsBaseChange`, `IsLocalization`). The unused hypotheses `R` Noetherian, `S` local Noetherian, `R → S` local and `S → S'` local are dropped; see the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 11.2.5 | `of_flat_quotient_of_tor_one_map_eq_zero` | case b), local rings |
| EGA | IV 11.3.12 | `of_flat_quotient_of_tor_one_map_eq_zero` | partial |
| EGA | IV 11.3.12 | `of_flat_quotient_of_tor_one_map_eq_zero_of_mem` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriterionVariant/BaseChangeSquare.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 11 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Flat.LocalCriterion.rTensor_subtype_map_injective_square`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
