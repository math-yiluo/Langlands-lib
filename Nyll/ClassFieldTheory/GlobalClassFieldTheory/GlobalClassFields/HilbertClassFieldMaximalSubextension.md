# The big Hilbert class field is the maximal abelian extension unramified at finite primes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldMaximalSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field. The library selects a big Hilbert class field `bigHilbertClassField K`, the class field of the big Hilbert norm subgroup, whose quotient is the narrow class group. This file proves that it is the maximal finite abelian extension of K unramified at every finite prime. That is, every such extension E/K admits a K-embedding into it.

## Main definitions and results

- `bigHilbertNormSubgroupInRationalClassFormation K₀`: for a finite abstract base field K₀ (a closed subgroup of finite index in Gal(ℚ̄/ℚ)), the big Hilbert norm subgroup of its fixed field, transported into the rational idèle-class formation.
- `bigHilbertClassFieldSubextension_normSubgroup`: the abstract norm subgroup of the selected big Hilbert subextension is exactly this transported subgroup.
- `bigHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_unramifiedAtFinitePlaces`: if the actual fixed-field extension of a finite abelian subextension P is unramified at all finite places, then P's norm subgroup contains the big Hilbert subgroup.
- `finiteUnramifiedAbelianSubextension_le_bigHilbertClassFieldSubextension` and `bigHilbertClassFieldSubextension_isFiniteUnramifiedAndMaximalAbelian`: `bigHilbertClassField K` is unramified at finite places over K, and, over the selected copy of K inside ℚ̄, the big Hilbert subextension lies above every finite abelian subextension whose fixed-field extension is unramified at finite places.
- `bigHilbertClassFieldCompatibleEmbedding K E` and `bigHilbertClassFieldEmbeddedAbelianSubextension K E`: a chosen embedding of E into ℚ̄ extending the base embedding of K, and E seen as an abstract finite abelian subextension.
- `finitePlaceUnramifiedness_congrTop`: unramifiedness at finite places is invariant under K-isomorphism of the top field.
- `finiteUnramifiedAbelianExtensionEmbeddingIntoBigHilbertClassField` and `finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField`: a K-algebra embedding E → `bigHilbertClassField K` for every finite abelian E/K unramified at finite places.
- `bigHilbertClassField_isMaximalUnramifiedAbelianExtension`: the big Hilbert class field is finite, abelian Galois, unramified at finite places, and receives a K-embedding from every finite abelian extension unramified at finite places.

## Proof

If E/F is unramified at every finite place, then no finite place of F is ramified. The imported `bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces` then puts the big Hilbert subgroup inside the idèle-class norm range of E/F. The order-reversing abstract classification (`FiniteAbelianSubextension.le_iff_normSubgroup_le`) turns this into containment of subextensions. Over the original K, E is placed in ℚ̄ compatibly with the selected copy of K, and the embedding is restricted to land in the class field.

## Points to watch

- "Unramified" means unramified at every finite prime (`IsUnramifiedAtFinitePlaces`). No condition is imposed at real places, which is why the maximal object is the big (narrow) Hilbert class field and not the ordinary one.
- Containment means existence of a K-algebra map. The embedding of E into ℚ̄ is a non-canonical choice made through `Classical.choose`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldMaximalSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `a8faacd90b23e6cb2749377ea3fd709b873e1f0e5b9b278afa6e8a39353a0da1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
