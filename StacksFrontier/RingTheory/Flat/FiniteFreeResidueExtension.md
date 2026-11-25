# Realizing residue field extensions by flat ring maps

Module `StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file realizes an arbitrary extension of the residue field of a local ring by a flat local ring map that does not change the maximal ideal.

- `IsLocalRing.exists_flat_residueField_algEquiv` takes a local ring R with maximal ideal 𝔪 and residue field k, and any field extension K of k, with no hypothesis on K/k. It gives a flat local R-algebra R′ whose maximal ideal is 𝔪R′ and whose residue field is isomorphic to K as a k-algebra. R and K may lie in independent universes u and v; R′ lies in `Type (max u v)`.

The construction uses the good lifts of `StacksFrontier.RingTheory.Flat.LocalConstruction`: a `GoodLift A F` is a flat local A-algebra A′ with 𝔪_{A′} = 𝔪_A A′ together with a k-embedding of its residue field into F. Here good lifts form a category (`GoodLift.category`), whose morphisms `GoodLift.Hom` are local ring maps compatible with the maximal ideals, the structure maps and the embeddings into F; flatness is not asked of a morphism. Directed systems of good lifts have colimits (`GoodLift.hasColimit_of_directed`), and adjoining one element of F outside the range of the embedding is a successor structure (`GoodLift.succStruct`). Mathlib's transfinite iteration of it over a well-order of cardinality greater than that of `Set F` reaches a stage whose embedding is onto (`GoodLift.exists_surjective_ι`). This gives the result in one universe and in ring-map form (`exists_flat_of_residueFieldHom`), which `exists_flat_of_residueFieldHom'` transports across universes through `ULift`. All these auxiliary declarations are private.

The module docstring also describes a finite free realization of finite extensions of the residue field κ(p) at a prime (Tag 07NE) and lists the definitions and results it is built from; none of them is in the file.

The main result is Tag 03C3; the module docstring cites Tag 09E0 for its separable algebraic case. The flat local construction corresponds to EGA 0 10.3.1 and the first assertion of SGA 3 V 4.1.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [03C3](https://stacks.math.columbia.edu/tag/03C3) | `IsLocalRing.exists_flat_residueField_algEquiv` | The lemma's preamble, a local ring `R'` and a local ring map `R → R'`, is the `Algebra R R'`, `IsLocalRing R'` and `IsLocalHom (algebraMap R R')` binders; the conjuncts are flatness, `𝔪' = 𝔪 R'` as `Ideal.map`, and `k' ≅ K` as an extension of `k` as an `≃ₐ[ResidueField R]`. `K` is allowed to live in a universe of its own, the source's case being `v = u`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 10.3.1.4 | `exists_surjective_ι` | terminal ring B=A_γ |
| SGA | 3 V 4.1.2 | `exists_surjective_ι` |  |
| EGA | 0 10.3.1 | `exists_flat_of_residueFieldHom` | partial |
| EGA | III 4.3.4 | `exists_flat_of_residueFieldHom` | partial |
| EGA | 0 10.3.1 | `exists_flat_of_residueFieldHom'` | partial |
| SGA | 3 V 4.1.2 | `exists_flat_of_residueFieldHom'` |  |
| SGA | 3 V 4.1.2 | `IsLocalRing.exists_flat_residueField_algEquiv` | first assertion |
| EGA | 0 10.3.1 | `IsLocalRing.exists_flat_residueField_algEquiv` | flat local ext, k'≅K |
| EGA | III 4.3.4 | `IsLocalRing.exists_flat_residueField_algEquiv` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/FiniteFreeResidueExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 47 declarations of the source file 22 are kept. The 25 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 6 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 9 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
