# A finite set inside a whole section generation open of an ample line bundle

`Langlands.AlgebraicGeometry.Picard.ampleFiniteSetSection` proves exactly the
published `AmpleFiniteSetSectionStatement.{u}` for arbitrary universe `u`.
Import it from
`Langlands.AlgebraicGeometry.Picard.AmpleFiniteSetSectionProof`.
For every scheme `X`, line bundle `L`, proof `hL : L.IsAmple`, finite set
`E : Set X` and open `W` containing `E`, it gives `n ≥ 1` and an actual
global section `s : L.powSections n` with
`E ⊆ (L.sectionOpen s : Set X)` and `L.sectionOpen s ≤ W`.

The consumer `Langlands.AlgebraicGeometry.Picard.ampleFiniteSetSection_apply`
takes `X`, `L`, `hL`, `E`, `W`, `hE : E.Finite` and the containment proof
directly, and returns this existential conclusion.

## Implemented deduction

Fix the quantified scheme, line bundle, ampleness proof and finite-set/open
data. The theorem `ampleSectionOpenBasis` from
`Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof`, applied to
`X`, `L` and `hL`, has exactly the basis hypothesis needed by the published
`finiteSectionAvoidance` theorem from
`Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceProof`.
Applying that theorem to `E`, `W`, `hE` and the containment proof returns
the required positive exponent, section and two inclusions. The consumer is
the direct application of this unconditional theorem to its arguments.

The imported avoidance proof uses induction on the number of points,
transport to common positive degrees, additivity of residue values and the
specialization preorder. Its empty-set case uses the zero section in degree
one, whose whole generation open is empty. The present deduction retains
that case, including when `W` is empty.

All section spaces and whole maximal generation opens are the actual published
ones. Tensor powers retain their right-associated convention. The only
geometric premise is `L.IsAmple`; no affine neighborhood of the finite set or
additional geometric or avoidance hypothesis is required. The conclusion
makes no affineness assertion.

## Provenance and authorship

This is the explicit weakening of Stacks Lemma 28.30.6, tag
[09NV](https://stacks.math.columbia.edu/tag/09NV), that retains the two
inclusions and drops its affineness conclusion. The registered original is
`stacks-properties-chapter-2026-10-28`, *Properties of Schemes*, PDF compiled
July 14, 2026, SHA256
`2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`,
page 51 (Lemma 30.6). The current statement and comments were also read in
the registered `stacks-section-open-prerequisites-2026-10-29`.
The implemented avoidance route differs from the source's graded prime
avoidance proof, as explained in the published avoidance companion.

Worker 689 wrote this assembly, consumer and explanation. The avoidance
proof is reused as the published theorem of Worker 869; the basis proof and
its geometric dependencies are imported by their Lean names.
