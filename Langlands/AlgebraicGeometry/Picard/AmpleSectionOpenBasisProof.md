# Whole section generation opens of an ample line bundle form a basis

`Langlands.AlgebraicGeometry.Picard.ampleSectionOpenBasis` proves exactly the
published `AmpleSectionOpenBasisStatement.{u}` for arbitrary universe `u`.
Import it from
`Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof`.
For every scheme `X`, line bundle `L`, proof `hL : L.IsAmple`, open `W`
and point `x ∈ W`, it gives a positive integer `n` and an actual global
section `s : L.powSections n` with
`x ∈ L.sectionOpen s` and `L.sectionOpen s ≤ W`.

The consumer `Langlands.AlgebraicGeometry.Picard.ampleSectionOpenBasis_apply`
takes `X`, `L`, `hL`, `W`, `x` and the membership proof directly, and returns
this displayed existential conclusion by applying the main theorem.

## Quasi-separatedness from ampleness

`LineBundle.IsAmple.quasiSeparatedSpace` chooses, for each point, the affine
whole generation open of a section of a positive tensor power supplied by
ampleness. These opens cover the scheme. Each pairwise intersection is affine
by the published `affineGenerationLocusIntersection`, applied to the line
bundle underlying the second section's actual tensor power.
`tensorPow_isLocallyFreeRankOne` supplies its rank-one property.
Every affine open is compact, so
`Scheme.quasiSeparatedSpace_of_isOpenCover` concludes that `X` is
quasi-separated.

This is the affine-cover argument of Stacks Lemma 28.27.7, tag
[01PY](https://stacks.math.columbia.edu/tag/01PY). Compactness of `X` is
supplied separately by `hL.compactSpace` in the basis proof. Thus both qcqs
hypotheses needed for principal lifting follow from the given ampleness.

## The basis proof

At `x`, `hL.exists_section` supplies `n ≥ 1`, a section of `L^{⊗n}`, and
its affine whole generation open containing `x`. Mathlib's
`IsAffineOpen.exists_basicOpen_le` refines that open by `X.basicOpen r`,
containing `x` and contained in `W`, for a regular function `r` on the
original generation open.

Apply the published unconditional
`Langlands.SchemeModule.principalGenerationOpenLift` from
`Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftProof` to
the line bundle with underlying module `tensorPow L.obj n`. It supplies
`m ≥ 1` and a global section `t` of its actual `m`th tensor power whose
whole generation open equals `X.basicOpen r`.

The published `tensorPowMulIso L.obj n m` transports `t` to a section of
`L.powSections (n * m)`. The theorem `trivializationOpen_mapIso` from
`Picard.AmpleIsoProof` identifies its entire generation open with that of
`t`, hence with `X.basicOpen r`. Both requested inclusions follow from the
chosen principal refinement. The inequality `1 ≤ n * m` follows by
multiplying `1 ≤ n` and `1 ≤ m`.

The theorem retains the published right-associated tensor powers and whole
maximal generation opens. It applies to arbitrary schemes and arbitrary opens,
and adds no geometric hypotheses to `L.IsAmple`. Its type is the published
proposition itself, with every prerequisite discharged by a proved theorem.

## Provenance and authorship

This proof implements the neighborhood form of the implication (1) to (3)
in Stacks Proposition 28.27.13, tag
[01Q3](https://stacks.math.columbia.edu/tag/01Q3), whose item (3) is
[01Q6](https://stacks.math.columbia.edu/tag/01Q6).
The registered source is `stacks-properties-chapter-2026-10-28`,
*Properties of Schemes*, PDF compiled July 14, 2026, SHA256
`2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`,
pages 44–45 (Proposition 27.13).
The principal-lifting dependency implements the scalar denominator-clearing
route from Lemma 28.18.2, tag
[01PW](https://stacks.math.columbia.edu/tag/01PW), PDF pages 22–23,
and a whole-locus calculation. The current HTML passages and comments at
01Q3, 01Q6, 01PY and 01PW were read in the registered
`stacks-section-open-prerequisites-2026-10-29`; the corrected common-exponent
argument in the 01PW comments is implemented in the published clearing proof.

Worker 689 wrote the quasi-separatedness lemma, basis assembly, consumer and
this explanation. The principal-lifting, affine-intersection, tensor-rank and
isomorphism-transport results are reused by their published Lean names.
