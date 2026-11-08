# Discrete decomposition of `L²` on a compact left coset space

`Langlands.QuotientIntegration.CompactQuotientDiscreteDecompositionStatement`
is a proposition definition. It supplies no proof.

## Setting

- `G` is a Hausdorff, locally compact, second countable topological group
  with its Borel σ-algebra. `μG` is a left Haar measure on `G`. No
  separate unimodularity hypothesis appears, but the compatibility
  hypothesis below already forces `G` to be unimodular (see the remark
  after the setting).
- `H` is a closed subgroup of `G`, with Borel σ-algebra. Its measure `μH`
  is s-finite, right invariant and finite on compact sets.
- `ν` is a measure on the left coset space `LeftQuotient H` (cosets `H g`)
  that is finite on compact sets and satisfies the existing compatibility
  predicate `IsCompatible H μG μH ν`. That predicate includes right
  invariance and the Weil integration formula.
- `LeftQuotient H` is compact.
- `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` preserves inner products, has
  continuous orbits `g ↦ π g x`, and represents each `π g φ` `ν`-almost
  everywhere by `q ↦ φ (rightTranslate H g q)`. So `π` is the original
  unitary right regular representation, given by its defining properties.

Remark on unimodularity. `IsCompatible` requires `ν` to be right
invariant and to satisfy the unweighted Weil formula
`∫ quotientAverage f dν = ∫ f dμG` for continuous compactly supported
`f`. The Library lemma `quotientAverage_rightTranslate` gives
`quotientAverage f (rightTranslate H g q) = quotientAverage (x ↦ f (x * g)) q`.
Hence `∫ f (x * g) dμG = ∫ f dμG` for all such `f`, so the regular
measure `μG` is also right invariant. Every instance of the hypotheses
therefore has unimodular `G`. The statement does not cover nonunimodular
groups.

## Conclusion

There is a set `A` of closed subspaces of `Lp ℂ 2 ν` with three properties.

1. Every `P ∈ A` is nonzero, closed and `π`-invariant, and it is
   topologically irreducible: every closed `π`-invariant subspace
   contained in `P` is `⊥` or `P`.
2. The inclusions of the members of `A` form a Hilbert sum of the whole
   space, in Mathlib's sense `IsHilbertSum`. That is, they are mutually
   orthogonal, and the closure of their span is all of `Lp ℂ 2 ν`.
3. Every member has finite multiplicity. For `P ∈ A`, only finitely many
   `Q ∈ A` admit a linear isometric equivalence `P ≃ₗᵢ[ℂ] Q` that
   intertwines the restricted actions.

This is a decomposition into irreducible unitary representations with
finite multiplicities. It is not a classification of the summands, and
`A` is not asserted to be unique. No trace-class property, character
formula or automorphic specialization is asserted. One universe carries
`G`, its subgroup and the quotient.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Corollary 9.1.3, printed p.241 (one-based PDF p.253), states that the
  cuspidal subspace decomposes into a Hilbert direct sum of irreducible
  representations, each with finite multiplicity.
- Lemma 9.3.1 and Corollary 9.3.2, printed p.247 (one-based PDF p.259),
  derive this from compactness of convolution operators.

When the quotient is compact, every convolution operator is compact on the
whole `L²` space, so the whole space decomposes. For a connected reductive
group with compact `[G]`, this is the full `L²` decomposition, where
cuspidal and discrete spectra coincide. The statement generalizes that
case to an arbitrary closed subgroup `H` of a (necessarily unimodular)
group `G` with compact left coset space and a compatible quotient measure.

The Library's `PositiveRationalQuotient`, whose measure satisfies
`IsCompatible` by `positiveRationalQuotientHaarMeasure_isCompatible`, is
the intended specialization. That specialization still requires
compactness of the actual quotient, which is a separate reduction-theory
input.

## Intended proof

A private proof compiles. Besides published results, it uses only the
staged statements `IntegratedTranslationPointwiseStatement` and
`CompactQuotientIntegratedHilbertSchmidtStatement`.

1. The published `rightHaarHermitianApproximation` gives continuous,
   compactly supported, nonnegative weights. Their integrated operators
   `T n` for the right Haar measure `μG.inv` are symmetric and converge
   strongly to the identity. They also preserve closed invariant
   subspaces and commute with intertwining isometries.
2. The published `haarInversionDensity` writes `μG.inv` as `μG` with the
   modular character as density. So each `T n` is the left-Haar integrated
   operator of the compactly supported continuous weight
   `modularCharacter · f n`.
3. The compact-quotient Hilbert–Schmidt statement and the published
   `hilbertSchmidtCompact` make each `T n` compact.
4. The published `compactApproximationOrthogonal`, applied to the whole
   space, gives the orthogonal irreducible family and the density of its
   span. Mathlib's `IsHilbertSum.mkInternal` packages these. The
   published `compactApproximationMultiplicity` gives finite
   multiplicities.
