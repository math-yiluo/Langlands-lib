# Schur averaging for continuous complex compact representations

Authors: Worker 94 (original pair) and Worker 86 (explicit context parameters).

`Langlands.Representation.CompactSchurAveragingStatement G` concerns an
arbitrary compact topological group in an arbitrary universe, with its
Borel measurable structure. For every continuous complex representation
`ρ` on the canonical finite-dimensional space `Fin d → ℂ` which is
algebraically irreducible, every left invariant probability measure `ν`,
every complex linear endomorphism `T`, and every vector `v`, it asserts

`d • ∫ k, ρ(k) (T (ρ(k⁻¹) v)) dν(k) = trace(T) • v`.

The declaration explicitly binds `G` and its `Group`, `TopologicalSpace`,
`IsTopologicalGroup`, `CompactSpace`, `MeasurableSpace`, and `BorelSpace`
instances, retaining the compact topological group and Borel compatibility
in its complete type.

The integral takes values in the finite-dimensional normed vector space.
There is no integration in an arbitrary locally convex representation.
The dimension may be zero in the quantifiers; the irreducibility premise
then has no instance. No unitarity, chosen invariant inner product, right
invariance, or smoothness assumption is imposed.

This is an internal prerequisite for the actual archimedean compact-type
projector. Its provenance is the algebraic scalar-commutant version of
Schur's lemma already implemented by Mathlib as
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`,
together with finite-dimensional integration and the cyclic matrix trace.
The proposed argument averages the conjugates of `T`, uses left invariance
to show that the resulting endomorphism intertwines `ρ` with itself, and
uses irreducibility over `ℂ` to make it scalar. Taking traces determines
the scalar without division by the dimension. This module states that
consequence; it contains no proof of the averaging formula.

Applied to rank-one endomorphisms and summed over a basis, the formula is
intended to supply inverse-character reproduction on the source type.
That application, the actual compact-type projector, finite multiplicity,
Lie-orbit density, and automorphic differential growth remain separate
proof obligations.
