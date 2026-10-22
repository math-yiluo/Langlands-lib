# A compact archimedean representative set

Author: Worker 212. This internal construction uses the actual
infinite adele topology and Mathlib's existing mixed-space lattice of algebraic
integers. It introduces no approximation hypothesis.

The existing homeomorphism `infiniteAdeleHomeomorph`, imported from
[ArchimedeanGL](ArchimedeanGL.md), packages the same function as
`NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`. It splits the coordinates
into real and complex places and uses the existing isometric equivalences of
the completions with the real and complex fields. In particular, continuity in
both directions refers to the original product topology.

`archimedeanFundamentalSet` is the inverse image, expressed as an image under the
inverse homeomorphism, of the closed parallelepiped of
`NumberField.mixedEmbedding.latticeBasis`. This parallelepiped is compact, so
its continuous image is compact.

The reduction theorem uses `ZSpan.exist_unique_vadd_mem_fundamentalDomain` to
translate the mixed-space point into the half-open fundamental domain by a
lattice element. `mem_span_latticeBasis` identifies the lattice element with
the image of an algebraic integer. Negating that integer gives the subtraction
convention of the theorem. The half-open fundamental domain lies in the closed
parallelepiped, so the translated infinite adele lies in the compact set.

The homeomorphism and its comparison lemmas require only a field. The compact-set
construction and reduction theorem require a number field. They allow arbitrary
universes and use no additional hypotheses. This is derived
content based on Mathlib's `NumberTheory/NumberField/InfiniteAdeleRing.lean`,
`NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`, and
`Algebra/Module/ZLattice/Basic.lean`.

This module supplies only the archimedean factor for the additive adele quotient
compactness argument. Finite-place approximation and quotient compactness are
separate obligations.
