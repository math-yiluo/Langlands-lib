# Finite center-span coverings of actual generated compact types

Author: Worker 94.

`Langlands.Global.ArchimedeanGL.CompactTypeCentralSpanStatement K n`
is an internal algebraic prerequisite for admissibility. It uses every number
field in arbitrary universe and every natural rank, including zero. Its
objects are the published actual compact group, continuous irreducible
compact types, smooth functions and complex enveloping differential action.

For a smooth vector `f` with finite-dimensional actual compact orbit, write
`M` for the complex span of all `compactAction k (operator a f)`, where `k`
ranges over the whole standard compact subgroup and `a` over the full
enveloping algebra. For every actual compact type `σ`, the proposition asks
for a natural number `m` and vectors `v i` in `M` such that the intersection
of `compactTypeSubmodule σ` with `M` is contained in the sum of their full
center-orbit spans. The finite supremum of submodules in Lean is that sum.
The published linear equivalence `toSmooth` transports each published
`centerOrbitSpan` back to the derivative-topology carrier.

There is no center-finiteness assumption on `f`, and no complex
finite-dimensionality conclusion. In particular, this proposition does not
assume the admissibility result it is intended to help prove. The spanning
vectors belong to the actual generated module. They need not belong to
`σ`, and equality with the sum of their center spans is not asserted.
This covering formulation needs no premise that disconnected compact
conjugation fixes the center pointwise or preserves a selected type.

The motivating algebraic source is Harish-Chandra, *Representations of a
semisimple Lie group on a Banach space I*, Theorem 1, printed page 195 /
one-based PDF page 11, with proof on printed pages 195–200. The registered
source is
`provided-3653f29ecd116fbb8becf37a078787d768f76f5b4bc4b075c85b5b9647628636`,
retained at
`/home/taskhub/pilot/literature/Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Trans. AMS 75 (1953).pdf`.
That theorem assumes a semisimple Lie algebra and a finite-dimensional
semisimple quotient for the compact-Lie enveloping subalgebra. It proves
finite generation of simple compact-Lie isotypic parts of the induced
enveloping module over its center. It does not by itself state this
number-field GL covering proposition. The passage to the reductive center,
finite products, disconnected compact factors, actual compact-group types
and the actual generated module remains to be proved.

The intended later application adds center finiteness of `f`. A separate
common-annihilator construction supplies one finite-codimensional center
ideal killing every vector of `M`. Each center span above is then an image
of the same finite-dimensional center quotient. The finite sum is
finite-dimensional, and so is its compact-type subspace. This explains the
covering target without asserting its proof or presupposing admissibility.

This pair defines only the proposition. It proves neither the covering nor
finite multiplicity, passage to a closed group module, analyticity,
convolution reproduction or automorphic differential growth.
