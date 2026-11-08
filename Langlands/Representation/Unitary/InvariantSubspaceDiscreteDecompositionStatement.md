# Discrete decomposition of an invariant subspace with compact convolutions

`Langlands.Analysis.InvariantSubspaceDiscreteDecompositionStatement` is a
proposition definition. It supplies no proof.

## Setting

- `G` is a Hausdorff, locally compact, second countable topological group
  with its Borel σ-algebra and a left Haar measure `μ`. No unimodularity is
  assumed.
- `E` is a complex Hilbert space.
- `π : G →* (E →L[ℂ] E)` preserves inner products and has continuous
  orbits `g ↦ π g x`. The statement derives from these the norm
  preservation and orbit measurability required by the existing
  `integratedIsometricAction`.
- `V` is a closed `π`-invariant subspace of `E`.
- For every compactly supported continuous `f : C_c(G, ℂ)`, the
  restriction to `V` of the integrated operator `R(f) = ∫ f(g) π(g) dμ(g)`
  is compact. Formally, `R(f).comp V.subtypeL : V →L[ℂ] E` is a compact
  operator.

## Conclusion

There is a set `A` of closed subspaces of `E` with four properties.

1. Every `P ∈ A` lies in `V`, is nonzero, closed and `π`-invariant, and is
   topologically irreducible: every closed invariant `Q ≤ P` is `⊥` or `P`.
2. The members of `A` are pairwise orthogonal.
3. The closure of their span is exactly `V`.
4. Each member has finite multiplicity. For `P ∈ A`, only finitely many
   `Q ∈ A` admit a `π`-intertwining linear isometric equivalence
   `P ≃ₗᵢ[ℂ] Q`.

`A` is not asserted to be unique, and no classification or trace-class
property is claimed. The universes of `G` and `E` are independent.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Lemma 9.3.1 and Corollary 9.3.2, printed p.247 (one-based PDF p.259),
  pass from compact convolution operators on a closed invariant subspace to
  a Hilbert direct sum of irreducibles with finite multiplicities.
- Corollary 9.1.3, printed p.241 (one-based PDF p.253), applies this to the
  cuspidal subspace, using Theorem 9.1.2.

This statement is that passage in abstract form. The intended application
takes `V` to be the closed cuspidal subspace of `L²([G])`. Corollary 9.1.3
then follows from compactness of `R(f)` on that subspace. Compactness
itself, GH Theorem 9.1.2, is not assumed anywhere else and is not proved
here. The statement asks for compactness for compactly supported continuous
weights, where GH uses smooth test functions.

## Intended proof

A private proof compiles. It uses only published results.

1. The published `rightHaarHermitianApproximation` gives symmetric
   approximate identities `T n` for the right Haar measure `μ.inv`. They
   converge strongly to the identity, preserve closed invariant subspaces
   and commute with intertwining isometries.
2. The published `haarInversionDensity` identifies each `T n` with the
   left-Haar integrated operator of a compactly supported continuous
   weight. So the hypothesis makes `T n` compact on `V`.
3. Restrict `π` and the `T n` to the Hilbert space `V`. Closed invariant
   subspaces of `V` are exactly the closed invariant subspaces of `E`
   contained in `V`. Intertwining isometries correspond through the
   isometric identification of a subspace of `V` with its image in `E`.
4. The published `compactApproximationOrthogonal` and
   `compactApproximationMultiplicity`, applied to `V`, give the family and
   its finiteness. Their images in `E` give `A`.
