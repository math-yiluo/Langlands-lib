# Integrals over a quotient through a compact open subgroup

`Langlands.Analysis.Local.QuotientCompactOpenDescent`. Namespace `Langlands.QuotientIntegration`.

An orbital integral over `S \ G` of a function supported near `j(H)` is an orbital integral over
`T \ H` of its average over a compact open subgroup `K` of `G`. In the matching of test functions
near the identity for base change, `G = GL_n(E)`, `H = GL_n(F)`, `j = baseChange`, `S` the
σ-centralizer of a rational element and `T` the centralizer of its norm in `GL_n(F)` (and, for the
ordinary orbital integral, `G = H`, `j = id`).

## Statement

`IsCompatible.integral_descend_eq_of_compactOpen`. Hypotheses:

- `G`, `H` groups that are topological groups, Hausdorff, locally compact, second countable, with
  Borel σ-algebras; `j : H →* G` with `IsClosedEmbedding j`;
- `μG : Measure G` left invariant and finite on compacts; `μH : Measure H` left invariant, finite on
  compacts and positive on open sets;
- `K : Subgroup G` open and compact;
- `T : Subgroup H` closed and `S : Subgroup G` with `S = T.map j`, both with Borel σ-algebras;
  `μS : Measure S`, `μT : Measure T` right invariant, finite on compacts, positive on open sets, with
  `μS.map Subtype.val = μT.map fun t : T => j t`;
- quotient measures `νS` on `LeftQuotient S`, `νT` on `LeftQuotient T` (Borel) with
  `IsCompatible S μG μS νS` and `IsCompatible T μH μT νT`;
- `Φ : G → ℂ` measurable with `Φ (s * g) = Φ g` for `s ∈ S`, `Φ g ≠ 0 → ∃ h κ, κ ∈ K ∧ g = j h * κ`,
  and `Integrable (descend S Φ hΦS) νS`;
- `Ψ : H → ℂ` with `Ψ h = ∫ κ in K, Φ (j h * κ) ∂μG` and `Ψ (t * h) = Ψ h` for `t ∈ T`.

Conclusion:
`∫ q, descend S Φ hΦS q ∂νS = (μH (K.comap j)).toReal⁻¹ • ∫ q, descend T Ψ hΨT q ∂νT`.

No inversion invariance or unimodularity is assumed, and no integral is defined by a choice.

## Proof

Let `ρ` be a continuous normalizing function of `T` (`exists_continuous_isNormalizingFunction`) and
put `b g = ∫⁻ h, ρ h · 1_K (j(h)⁻¹ g) dμH` and `c = μH (K ∩ H)` (`0 < c < ∞`).

1. `μG.withDensity b` is the image of `(μH.withDensity ρ) ⊗ μG|_K` under `(h, κ) ↦ j(h) κ`
   (Tonelli and left invariance of `μG`).
2. For `g = j(h₀) κ₀` with `κ₀ ∈ K`: `∫⁻ t, b (j(t) g) dμT = c` (left invariance of `μH`, Tonelli,
   and the normalization of `ρ`); by `μS ↔ μT`, `∫⁻ s, b (s g) dμS = c`. Off the open set `j(H) K`,
   `b = 0`.
3. Hence `b / c` on `j(H) K`, glued with any normalizing function of `S` outside, is a normalizing
   function of `S`. By the rule of `QuotientNormalizingFunction` (`IsCompatible.integral_descend_eq`)
   and step 1, `∫_{S\G} Φ dνS = c⁻¹ ∫ Φ d(μG.withDensity b) = c⁻¹ ∫∫ Φ(j(h) κ) ρ(h) dμG|_K dμH`;
   integrability on the product comes from that of the descent of `Φ`
   (`IsCompatible.integrable_descend_iff`). The last integral is `∫_{T\H} Ψ dνT` by the same rule
   for `T`.

## Declarations, in order

private `compactOpenDensity`, `measurable_compactOpenDensity`, `compactOpenDensity_eq_zero`,
`withDensity_compactOpenDensity`, `lintegral_compactOpenDensity_eq`; public
`IsCompatible.integral_descend_eq_of_compactOpen`.

## Literature

J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), Chapter 1, §3, proof of Lemma 3.4, pp. 22–23: a function `α ∈ C_c^∞(G(E))` with
`∫_{M(F)} α(mg) dm = 1` on the relevant set, `ψ(m) = ∫_{G(E)} α(g) φ(g⁻¹ m⁻¹ δ₀ g^σ) dg`, and the
change of variables `g ↦ m₁ g` "grouping the integrals along `M(F)`" (p. 23). Here
`α = c⁻¹ 1_K` restricted to the relevant orbit, and the grouping is the rule for normalizing
functions. For a single orbit `H g K` the Library's `CompactOpenOrbitMeasureStatement`
(`QuotientCompactOpenOrbitStatement.lean`) describes the restriction of a compatible measure; it is
not used here.

## Source and licence

Restates `UpperTheory.ConvolutionTheory.Loc.quotDesc` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>)
at commit `f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`, file
`src/Development/AutomorphicArithmetic/Foundations/Convolution/TwistedLocalOrbits/QuotDesc.lean`
lines 43–84 (`lintegral_desc`) and 167–206 (`quotDesc`), with a new proof. The repository has no
licence file; its text is used with attribution (see
`licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- The source's integrals `quotIntegral` (against a normalizing function chosen by `Classical.choice`)
  are replaced by integrals against compatible quotient measures (`IsCompatible`), as everywhere in
  the Library's orbital integrals.
- The source compares two arbitrary normalizing functions (`swap_fibre`), which needs an
  inversion-invariant `μT`; here the normalizing function of `S` is built from the one of `T`
  (the density `b`, the source's `b` in `lintegral_desc`), and the BCU rule
  (`IsCompatible.integral_descend_eq`) makes the comparison unnecessary. The hypotheses
  `μT.IsInvInvariant`, `μG.IsMulRightInvariant`, `μH.IsMulRightInvariant` of the source are dropped;
  `μS`, `μT` are required to be positive on open sets (for the existence of normalizing functions).
- The source's integrability hypothesis (a compact `D` with `Φ` supported in `S · D`, and
  `mass_ne_top`) is replaced by integrability of the descended function, from which integrability on
  the product is derived (the source's pushforward argument `hm` is replaced by `integral_prod`).
- The function `Ψ` and its `T`-invariance are explicit arguments.
