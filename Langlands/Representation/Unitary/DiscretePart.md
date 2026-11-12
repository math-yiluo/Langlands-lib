# Irreducible subrepresentations and the discrete part

Module `Langlands.Representation.Unitary.DiscretePart` defines, for a
representation `ρ : Representation ℂ H E` of a monoid `H` on a complex inner
product space `E`, the irreducible subrepresentations of `ρ` and its discrete
part. It is a definition module and proves nothing.

## Source

Getz–Hahn, *An introduction to automorphic representations*, registered as
`getz-hahn-2024-automorphic-representations`, §9.1 (9.6), p.242 (PDF
page 254): the discrete spectrum `L²_disc([G]) ≤ L²([G])` "is the largest
closed subspace of `L²([G])` that decomposes as a Hilbert space direct sum
of irreducible subrepresentations of `L²([G])`". Subrepresentations of a
unitary representation are closed invariant subspaces.

## Definitions

- `Langlands.Analysis.IsIrreducibleSubrepresentation ρ V`: the subspace
  `V : Submodule ℂ E` is closed, nonzero and `ρ`-invariant, and every closed
  `ρ`-invariant subspace `W ≤ V` is `⊥` or `V`.
- `Langlands.Analysis.discretePart ρ`: the topological closure of the
  supremum (the sum) of all irreducible subrepresentations of `ρ`.

## Correspondence with the source

The two descriptions agree for a unitary representation `ρ` on a Hilbert
space `E`. This is explanatory and not proved here.

- A closed subspace that is a Hilbert direct sum of irreducible
  subrepresentations is the closure of their sum, so it lies in
  `discretePart ρ`.
- Conversely, choose by Zorn's lemma a maximal family of mutually orthogonal
  irreducible subrepresentations `V_i`, and let `W` be the closure of their
  sum. `W` and `W^⊥` are invariant and the orthogonal projection onto `W^⊥`
  commutes with `ρ`. If an irreducible subrepresentation `V` were not
  contained in `W`, the restriction `T : V → W^⊥` of this projection would
  be a nonzero intertwining operator. By Schur's lemma for irreducible
  unitary representations, `T* T` is a positive scalar, so `T` is a multiple
  of an isometry and its image is an irreducible subrepresentation in
  `W^⊥`, contradicting maximality. So `discretePart ρ = W`
  is itself a Hilbert direct sum of irreducible subrepresentations and is
  the largest such subspace.

For a unitary representation, invariance under `ρ h` for all `h` implies
invariance under the adjoints `ρ h⁻¹`, so "invariant" may be read in either
sense. No continuity of `ρ` is required by the definitions; for the right
regular representation on `L²([G])` it holds.

## Use

`Langlands.Global.AdelicGroupPoints.discreteSpectrum` (module
`Langlands.Global.AdelicParabolicSpectrum`) applies `discretePart` to the
right regular representation of `G(𝔸)` on `L²([G])`. The condition
`IsIrreducibleSubrepresentation` is the one written out inline in
`Langlands.Analysis.InvariantSubspaceDiscreteDecompositionStatement`
(module `Langlands.Representation.Unitary.InvariantSubspaceDiscreteDecompositionStatement`)
for the members of its decomposition.
