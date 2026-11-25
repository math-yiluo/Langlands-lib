# Kaplansky’s theorem for local rings

Module `StacksFrontier.RingTheory.Module.Kaplansky`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Every projective module over a commutative local ring is free. The proof reduces to countably generated modules and constructs free direct summands containing prescribed elements.

`CountablyGenerated` requires a countable spanning set. `IsDirectSummandOf F N` means that some submodule G is disjoint from F and satisfies F ⊔ G = N, and `IsFreeDirectSummandOf` adds freeness of the summand. The file’s `PropertyP` asks that whenever M = N ⊕ N′ with N′ finite free, every element of N belongs to a free direct summand of N.

- `countablyGenerated_propertyP_free` proves freeness over a commutative ring from countable generation and `PropertyP`.
- `projective_local_free_summand` puts every element of a projective module over a commutative local ring in a free direct summand. `propertyP_of_projective` applies this to each complementary summand.
- `Module.free_of_projective_of_isLocalRing` proves freeness for any projective module over a commutative local ring, including infinitely generated ones.

For the countable argument, an increasing chain of finite free summands absorbs the generators in order, and its free increments form an internal direct sum. For a given element of a projective module, the proof minimizes the support of its image over splittings into a fixed free module. Minimality forces its nonzero coordinates to be a minimal generating family for their ideal. Locality then makes the matrix of projected basis vectors invertible on those coordinates, giving a basis and a projection onto its span. The imported decomposition theorem for projective modules supplies the countable reduction.

Kaplansky’s theorem is exposed as a theorem to invoke explicitly for a `Module.Free` instance.

Stacks Project, Tag 0591, Tag 0592, and Tag 0593. The countable reduction uses Tag 0590. The freeness theorem also refers to SGA 3 VIA 2.1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0591](https://stacks.math.columbia.edu/tag/0591) | `countablyGenerated_propertyP_free` |  |
| [0592](https://stacks.math.columbia.edu/tag/0592) | `projective_local_free_summand` |  |
| [0593](https://stacks.math.columbia.edu/tag/0593) | `Module.free_of_projective_of_isLocalRing` | Projective modules over local rings are free, with no finiteness hypothesis. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIA 2.1.3 | `Module.free_of_projective_of_isLocalRing` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Module/Kaplansky.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
