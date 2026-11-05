# Renard A.III.1: proof for the separated uniform completion

Author: Worker 1580.

This module proves the published proposition
`Langlands.Renard.UniformCompletion.UniformCompletionStatements.{u,v}`.
Its proof reuses Mathlib's actual Hausdorff completion, canonical map, extension,
and bundled categories. The statement and its dependencies are unchanged.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The right-universal definition is on printed p.251 / one-based PDF257;
the completion example is example 2 on printed p.252 / PDF258. These pages
were read directly for this proof. The derived uniform-space interpretation
and its restrictions are those of the published statement: maps are uniformly
continuous and targets are complete and separated. The printed continuous-map
topological-vector-space example and its linear-structure comparison remain
separate obligations.

`completionMap_proof` obtains completeness and separatedness from the actual
completion's instances. It uses `Completion.uniformContinuous_coe`,
`Completion.denseRange_coe`, and `Completion.isUniformInducing_coe` for the
canonical map. Only the final embedding clause passes the given source
`T0Space` hypothesis to `Completion.isUniformEmbedding_coe`.

`concreteExtension_proof` uses `Completion.uniformContinuous_extension` and
`Completion.extension_coe` to prove uniform continuity and agreement on source
points. It applies `Completion.extension_unique`, reversing the pointwise and
final equalities to match the target's orientation. This proof preserves the
independent source and target universes u and v, and imposes no separatedness
or nonemptiness on the source.

`categoricalExtension_proof` proves the factorization of the supplied
`UniformSpaceCat.extensionHom` through the supplied `completionHom` pointwise
using `Completion.extension_coe`. The existing completeness and separation
instances of the bundled target are supplied explicitly for its forgotten
uniform space. For uniqueness it unwraps the induced-category
morphism and applies `Completion.extension_unique`; the given categorical
equality supplies agreement at every canonical image. Both categories use the
same arbitrary carrier universe u, exactly as in the statement.

`rightUniversal_proof` constructs `Limits.IsInitial.ofUniqueHom` on the
structured arrow built from that same `completionHom`. For an arbitrary target
structured arrow, its morphism is `StructuredArrow.homMk` of the actual
`extensionHom`. The preceding categorical factorization establishes its
commuting triangle. Any other structured-arrow morphism has the same right
component by categorical uniqueness and `StructuredArrow.w`, so
`StructuredArrow.hom_ext` proves equality. This implements Renard's
right-universal factorization definition with the actual forgetful functor.

Finally, `uniformCompletionStatements_proof` conjoins these four proofs in the
published order. No metrizability, compactness, linearity, countability, or
nonemptiness premise is introduced. The proof route is an internal assembly
of Mathlib's completion results and structured-arrow initiality, rather than
an assertion that Renard separately states these four formal components.
