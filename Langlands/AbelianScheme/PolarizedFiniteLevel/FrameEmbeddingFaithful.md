# A frame-normalized datum is determined by its embedded image and torsion points

All schemes lie in one universe `u`.

## Declarations

- `Datum.torsionPoint_zero`: the torsion point with zero coefficients is the unit section.
- `Datum.torsionPoint_single`: the torsion point with the `i`-th unit coefficient tuple is
  the `i`-th level section.
- `Datum.nonempty_polarizedIso_of_realizes`: assume
  `CubicBundlePolarizationDeterminationStatement`. Let `a b` be data over a locally
  noetherian `S` with frame-normalized cubic embeddings `ψ`, `ψ'` for the same `ρ` that
  realize the same family `(I, σ)`. Then `a` and `b` are polarized-isomorphic.

## Proof of the main theorem

Both `ψ` and `ψ'` are closed immersions with kernel `I`, so
`φ := IsClosedImmersion.lift ψ' ψ` is an isomorphism `A_a ≅ A_b` with `φ ≫ ψ' = ψ`
(`IsClosedImmersion.isIso_lift`). It lies over `S`, and it carries every torsion point of
`a` to the torsion point of `b` with the same coefficients: both composites with the
monomorphism `ψ'` have the same projections to `S` and to `ℙ^m_ℤ` (the latter is `σ r`). In
particular `φ` preserves the unit section, so by the published rigidity theorem
`pointedMorphismRigidity` (a unit-preserving morphism from an abelian scheme to a group
scheme of finite presentation is a homomorphism; compare GIT p.131, "by Corollary 6.6, e
determines the group law") it is a homomorphism; it gives an
isomorphism of abelian schemes `e`. The level equations follow from `torsionPoint_single`.
For the polarization, the cubic conditions give `ψ^*𝒪(1) ≅ L_a³ ⊗ π^*N` and
`ψ'^*𝒪(1) ≅ L_b³ ⊗ π^*N'`; computing classes in the Picard group of `A_a`
(`LineBundle.classOf_tensor`, `classOf_inverse`, `Group.pullback_lineBundle_classOf`) gives
`φ^* L_b³ ≅ L_a³ ⊗ π^*(N ⊗ N'^{-1})`, and the polarization statement gives the polarization
equation.

## Provenance

GIT §7.2, printed p.131 (PDF p.144), registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`: "the whole
structure ... is determined only by (a) the embedding, (b) the 2g + 1 sections", with
Mumford's identity section and level sections replaced by all torsion sections. Part of
the reduction of `FrameChartRepresentabilityStatement` (`FrameChartRepresentabilityReduction`). What is not proved here: the
polarization statement itself, which is a named hypothesis.
