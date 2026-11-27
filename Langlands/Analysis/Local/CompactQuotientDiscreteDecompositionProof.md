# Discrete decomposition on a compact left coset space

The theorem `Langlands.QuotientIntegration.compactQuotientDiscreteDecomposition`
in this module proves
`Langlands.QuotientIntegration.CompactQuotientDiscreteDecompositionStatement`:
for a closed subgroup `H` of `G` with compact left coset space
`LeftQuotient H`, a compatible quotient measure `ν`, and the original unitary
right translation action `π` on `Lp ℂ 2 ν`, the space `Lp ℂ 2 ν` is a Hilbert
sum of topologically irreducible closed invariant subspaces, each isomorphism
class occurring only finitely often.

## The implemented proof

1. Inner-product preservation of each `π g` gives norm preservation, by
   Mathlib's `LinearMap.norm_map_iff_inner_map_map`. Continuity of each
   orbit `g ↦ π g x` gives the almost-everywhere strong measurability needed
   to define the Bochner-integrated operators. These are the same two
   derived hypotheses that `InvariantSubspaceDiscreteDecompositionStatement`
   builds from `hπinner` and `hπcont`.
2. The Library theorem `compactQuotientIntegratedHilbertSchmidt`
   (in `Langlands.Analysis.Local.CompactQuotientHilbertSchmidtProof`) makes
   the integrated operator `integratedIsometricAction μG π … f hf` of every
   integrable compactly supported continuous weight `f` Hilbert–Schmidt;
   it uses compactness of `LeftQuotient H`, the compatibility `hν` and the
   description of `π` as right translation. The Library theorem
   `hilbertSchmidtCompact` (in `Langlands.Analysis.HilbertSchmidtCompactProof`)
   makes each such operator compact. Composing with the inclusion of the
   whole space `⊤` keeps it compact (`IsCompactOperator.comp_clm`).
3. The Library theorem `invariantSubspaceDiscreteDecomposition` (in
   `Langlands.Representation.Unitary.InvariantSubspaceDiscreteDecompositionProof`),
   applied to the closed invariant subspace `⊤` with this compactness, gives
   a set `A` of nonzero, closed, invariant, topologically irreducible
   subspaces that are pairwise orthogonal, whose supremum has closure `⊤`,
   and in which every member has only finitely many isometrically
   intertwined copies.
4. Each member of `A` is closed in a complete space, hence complete. The
   pairwise orthogonality gives an `OrthogonalFamily` of the inclusions, and
   rewriting `sSup A` as the indexed supremum over `A` gives density of
   their span. Mathlib's `IsHilbertSum.mkInternal` packages these as the
   required `IsHilbertSum`. Irreducibility and finite multiplicity are taken
   unchanged from step 3; the condition `P ≤ ⊤` is dropped.

The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original source

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*
(2024), registered as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Corollary 9.1.3, printed p. 241 (one-based PDF p. 253), states that the
  cuspidal subspace is a Hilbert direct sum of irreducible representations,
  each with finite multiplicity.
- Lemma 9.3.1, printed p. 247 (one-based PDF p. 259), deduces such a
  decomposition with finite multiplicities for a unitary representation from
  compactness of the operators `R(f_n)` of a Dirac sequence, and
  Corollary 9.3.2 on the same page obtains that compactness from the trace
  class property, since trace class operators are Hilbert–Schmidt and
  Hilbert–Schmidt operators are compact.

The proof here follows the same pattern. The compact-quotient
Hilbert–Schmidt theorem plays the role of the trace class input and gives
compactness of every integrated operator on all of `L²`, not only on a
cuspidal subspace. The step of Lemma 9.3.1, from compact operators of an
approximate identity to a discrete decomposition with finite
multiplicities, is carried out in the Library by
`invariantSubspaceDiscreteDecomposition` (through
`compactApproximationOrthogonal` and `compactApproximationMultiplicity`),
which is applied here to the whole space.
