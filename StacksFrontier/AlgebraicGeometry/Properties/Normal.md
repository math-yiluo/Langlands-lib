# Normal schemes and their irreducible components

Module `StacksFrontier.AlgebraicGeometry.Properties.Normal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Normality is a condition on the local rings of a scheme. The file develops affine and open-cover tests and gives conditions for the irreducible components to form a disjoint union.

## Normality criteria

- `AlgebraicGeometry.IsNormal` is the library’s typeclass requiring every stalk to be a domain and integrally closed. `isNormal_iff_stalk_normal` expresses this as pointwise witnesses, and the stalk domain structure is available by instance inference.
- `isNormal_tfae` equates normality with normality of every affine section ring, normality of the section rings on some affine open cover, and the existence of an open cover by normal open subschemes. The ring predicate is `IsNormalRing`, defined by normality at prime localizations.
- `isNormal_open` and `isReduced_of_isNormal` give normality of open subschemes and reducedness of normal schemes. `isNormal_of_openCover` obtains normality from a cover by normal schemes.
- `isNormal_iff_forall_affineOpen_normal` says that an integral scheme is normal exactly when the section ring of every nonempty affine open is integrally closed.

The local criteria identify affine stalks with prime localizations and use invariance under open-immersion stalk isomorphisms.

## Decomposition

`isNormal_iff_exists_iso_coproduct` assumes every quasi-compact open has finitely many irreducible components. Under that hypothesis normality is equivalent to being isomorphic to a coproduct of normal integral schemes. Finite minimal primes on each affine open give a product of normal domains and hence irreducible open neighbourhoods. `component_eq_of_open_irreducible_nhd` then shows that components meeting the same irreducible open coincide, making the components open and pairwise disjoint. Conversely, a coproduct of normal schemes is covered by its summands, so `isNormal_of_openCover` makes it normal. The decomposition uses a cover index type in the scheme’s universe.

The module docstring also announces that the global sections of an integral normal scheme form a normal domain, and lists a separate lemma that a coproduct of normal schemes is normal; neither is in this file.

The file cites Stacks Project Tag 0309, Tag 033I, Tag 033J, Tag 033K, Tag 033L and Tag 0357. It also cites EGA 0 4.1.4, EGA 0 2.1.6, EGA II 7.3.7 and EGA IV 20.4.12.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [033I](https://stacks.math.columbia.edu/tag/033I) | `IsNormal` |  |
| [033J](https://stacks.math.columbia.edu/tag/033J) | `isNormal_tfae` | equivalent conditions |
| [033J](https://stacks.math.columbia.edu/tag/033J) | `isNormal_open` | open subschemes |
| [033K](https://stacks.math.columbia.edu/tag/033K) | `isReduced_of_isNormal` |  |
| [033L](https://stacks.math.columbia.edu/tag/033L) | `isNormal_iff_forall_affineOpen_normal` |  |
| [0357](https://stacks.math.columbia.edu/tag/0357) | `isNormal_iff_exists_iso_coproduct` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 7.3.7 | `isReduced_of_isNormal` | partial |
| EGA | IV 20.4.12 | `isReduced_of_isNormal` | partial |
| EGA | 0 2.1.6 | `component_eq_of_open_irreducible_nhd` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/Normal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 22 declarations of the source file 19 are kept. The 3 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.exists_global_of_mem_all_stalks`, `AlgebraicGeometry.isNormal_sigma`, `AlgebraicGeometry.normal_globalSections`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
