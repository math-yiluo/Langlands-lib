# Countably generated projective summands

Module `StacksFrontier.LinearAlgebra.DirectSum.ProjectiveCountablyGenerated`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Kaplansky's theorem decomposes a projective module over a ring into an internal direct sum of countably generated projective modules.

`Submodule.exists_sSupIndep_countable_span_projective_of_projective` shows that for a projective R-module M, there is an independent set of submodules of M with supremum ⊤, each countably generated and projective over R. The construction is in `Stacks.DirectSum.ProjectiveDecomposition.solution`.

Projectivity splits the canonical surjection from the free module `M →₀ R` to M. Its basis gives an internal direct sum of singly generated submodules. The auxiliary `exists_sSupIndep_countable_span_of_split` applies the countably generated direct-summand theorem to the complemented image of the section and transports the resulting decomposition back to M. Each resulting summand is a retract of M, with complement the supremum of the other summands, and hence is projective.

The theorem permits noncommutative rings. Countable generation is expressed by a countable subset of the ambient module M whose span is the summand, and independence is stated in the submodule lattice.

Tag 058Y gives the decomposition, using Tag 058X. Tag 058W and Tag 05A3 are cited for the formulation, and Tag 0590 and Tag 0593 for the connection with freeness. The file cites I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372–377.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [058Y](https://stacks.math.columbia.edu/tag/058Y) | `exists_sSupIndep_countable_span_projective_of_projective` | Being a direct sum of countably generated projective modules is written internally,   as in 058W and 058X: an independent set of submodules with supremum `⊤`, each spanned by a   countable set and each projective. Countable generation is a countable spanning set. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/LinearAlgebra/DirectSum/ProjectiveCountablyGenerated.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
