# The Kummer character for a radical generator

Module `StacksFrontier.FieldTheory.KummerExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

If L is generated over a field K by an n-th root of an element of K and K contains a primitive n-th root of unity, the Galois group is cyclic and the extension degree divides n. For a nonzero generator, the Kummer character realizes the group inside the roots of unity of K.

Given n ≠ 0, a primitive n-th root in K, and b ≠ 0 in L with bⁿ in the image of K, `Stacks.FieldTheory.KummerExtension.kummerCharacter` is a group homomorphism from the K-automorphisms of L to `rootsOfUnity n K`. The lemma `kummerCharacter_apply` identifies its value after embedding in L with σ(b)/b. The construction uses the equivalence between n-th roots of unity in K and L induced by the primitive root.

`isGalois_isCyclic_finrank_dvd_and_kummerCharacter_injective_of_adjoin_root_eq_top` assumes n ≥ 2 and `Algebra.adjoin K {b} = ⊤`. It gives finiteness, Galoisness, cyclicity, and divisibility of the degree by n. For b ≠ 0 it also proves injectivity and the formula for the character. Writing bⁿ = a in L, the proof realizes L as the splitting field of the separable polynomial Xⁿ − a when b ≠ 0. Equal character values force automorphisms to agree on the generator. When b = 0 the extension is trivial, and the theorem's character conclusion is conditional on b ≠ 0.

The extension result is Tag 09I6. The character is referenced to SGA 7 XV 3.3.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09I6](https://stacks.math.columbia.edu/tag/09I6) | `isGalois_isCyclic_finrank_dvd_and_kummerCharacter_injective_of_adjoin_root_eq_top` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 7 XV 3.3.2 | `kummerCharacter` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/KummerExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
