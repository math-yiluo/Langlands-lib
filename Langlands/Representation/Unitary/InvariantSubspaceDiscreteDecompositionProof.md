# Proof: discrete decomposition of an invariant subspace with compact convolutions

`Langlands.Analysis.invariantSubspaceDiscreteDecomposition` proves
`InvariantSubspaceDiscreteDecompositionStatement.{uG, uE}` using published
results only.

## Route

1. As in the compact-quotient case, the published
   `rightHaarHermitianApproximation` and `haarInversionDensity` give
   symmetric approximate identities `T n`. Each `T n` equals the left-Haar
   integrated operator of a compactly supported continuous weight. By the
   hypothesis, `(T n).comp V.subtypeL` is compact.
2. The proof restricts to the Hilbert space `V`, which is complete because
   it is closed.
   - The restricted representation `π'` and operators `T'` are
     `codRestrict`s of `π g ∘ V.subtypeL` and `T n ∘ V.subtypeL`.
   - Mathlib's `IsCompactOperator.codRestrict` makes `T'` compact.
   - Symmetry, strong convergence (`tendsto_subtype_rng`), and inner
     product preservation of `π'` are inherited.
3. A closed `π'`-invariant subspace `S'` of `V` maps to a closed
   `π`-invariant subspace of `E`, because `V.subtypeL` is a closed
   embedding. The last clause of `rightHaarHermitianApproximation` says
   that each `T n` preserves every closed `π`-invariant subspace and
   commutes with every `π`-intertwining isometry out of it. Therefore
   `T n` preserves the image, and `T'` preserves `S'`.
   Intertwining isometries between subspaces of `V` correspond to
   intertwining isometries between their images.
   `invariantSubspaceMapEquiv` is the isometric identification of a
   subspace of `V` with its image; it is built from
   `Submodule.equivMapOfInjective`.
4. The published `compactApproximationOrthogonal` (with `W = ⊤` in `V`) and
   `compactApproximationMultiplicity` apply to `(V, π', T')`. The required
   family `A` consists of the images of the resulting subspaces.
   - Irreducibility transfers by pulling back closed invariant subspaces
     with `comap`, together with `Submodule.map_comap_subtype`.
   - Orthogonality transfers through inner products of coercions.
   - Density holds because the closure of the image contains the image of
     the closure, and every member lies in the closed `V`.
   - Finiteness transfers through the injective image map.

The module also defines `invariantSubspaceMapEquiv` with its two
evaluation lemmas, `invariantSubspaceMapEquiv_apply` and
`invariantSubspaceMapEquiv_symm_apply`. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal proof, not a formalization of one cited source. It
combines the Library results named above with Mathlib. The argument is
the usual reduction of a discrete decomposition to compact self-adjoint
approximate identities. Here that reduction is applied inside the closed
subspace `V`.
