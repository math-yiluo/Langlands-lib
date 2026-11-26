# The cuspidal-pair Eisenstein series along Shahidi's line, from the general continuation

Module `Langlands.Global.Factors.CuspidalPairEisensteinLineContinuation` states and proves
`Langlands.Global.CuspidalPairEisenstein.CuspidalPairEisensteinLineReductionStatement.{u}`. This
is an implication with two premises, which the module does not prove:

- `EisensteinMeromorphicContinuationStatement.{u}`;
- `EisensteinJointRootHyperplaneStatement.{u}`.

The number field is `F : Type u` in an arbitrary universe.

## Statement

Assume the two premises for number fields in the universe `u`. Let `F : Type u` be a number field
with `[CompactSpace (AdeleQuotient F)]`, `r t : ℕ`, `N = r + t + 2`, and let
`T : CuspidalOperatorRealization F r` and `T' : CuspidalOperatorRealization F t`. Let `φ` satisfy
`IsSection T T' φ` (module `Langlands.Global.Factors.CuspidalPairEisensteinSeries`). Then there
are `E : ℂ → AdelicGL F N → ℂ` and `σ : ℝ` such that:

1. `E s = eisensteinSeries F φ s` whenever `σ < Re s`;
2. for every `s₀ ∈ ℂ` there are `m : ℕ`, an open `W ∋ s₀` and `h : ℂ → AdelicGL F N → ℂ` with
   - `h` continuous on `W × GL_N(𝔸)`;
   - `s ↦ h s g` complex differentiable on `W` for every `g`;
   - `h s (AdelicGL.rational F N x * g) = h s g` for `s ∈ W` and `x ∈ GL_N(F)`;
   - `h s g = (s - s₀)^m E s g` for `s ∈ W`, `s ≠ s₀`;
   - if the group-scheme Eisenstein series of the transported section `φ ∘ adelicHomeomorph F N`
     has `EisensteinLine.HasImaginaryAxisHolomorphy`, for the scheme block parabolic of type
     `(r + 1, t + 1)`, its presentation `blockRootData` and the standard maximal compact subgroup,
     and `Re s₀ = 0`, then `m = 0` and `h s₀ = E s₀`.

Clauses 1 and 2 without the last item are the first two clauses of
`CuspidalPairEisensteinJointContinuationStatement`, with the same `E`. The last item gives its
third clause under the stated hypothesis. Unitarity of the central characters is not assumed: it
enters only through that hypothesis.

## Implemented proof

The theorem `cuspidalPairEisensteinLineReduction` applies
`EisensteinLine.exists_lineContinuation_imaginary` (module
`Langlands.Global.AdelicEisensteinLineContinuation`). It uses the following data:

- the scheme `GL_N`, connected reductive by `isConnectedReductive_generalLinear`, with the smooth
  structure `smoothDimension_spec` and `adelicDifferentialCommutator_of_smooth`;
- the scheme block parabolic of type `(r + 1, t + 1)`, its block-unipotent radical
  (`blockUnipotentInclusion_isLeviGeometricUnipotentRadical`) and block Levi;
- the presentation `blockRootData`;
- the standard maximal compact subgroup (`isIwasawaCompact_blockParabolic`,
  `standardCompactPoints_isMaximalCompact`) and the standard matrix embedding;
- the transported section `φ ∘ adelicHomeomorph F N`, automorphic on the parabolic quotient by
  `isAutomorphicFunctionOn_of_isSection` (module `Langlands.Global.Factors.CuspidalPairSchemeAutomorphy`);
- the line parameter `λ₁ = lineParameter F r t = ((t + 1) det₁ - (r + 1) det₂) / N` (module
  `Langlands.Global.Factors.CuspidalPairSchemeSeries`).

The hypotheses on `λ₁` hold:

- **Root forms.** `λ₁` has real coefficients, so `B(λ₁, β)` is the real root form at `Re λ₁`
  (`rootFunctional_lineParameter`). This is `B(lineRestriction, β)`, which is positive for every
  root `β` of `A` in the unipotent radical by `weylInducedCharacterForm_lineRestriction_pos`
  (module `Langlands.Global.Factors.CuspidalPairLineRegularity`). So the root forms do not vanish at
  `λ₁` (`rootFunctional_lineParameter_ne_zero`).
- **Regularity.** `exists_isRegularParameter_lineParameter` (same module) gives, for every `R`, a
  `σ` beyond which `s λ₁` is `R`-regular.

For `Re s = 0`, `s = i·Im s`, so `s λ₁` is the imaginary parameter of
`Im s · Re λ₁` (`smul_lineParameter_mem_range_imaginaryParameter`).

The result is transported to matrices along the continuous multiplicative equivalence
`adelicHomeomorph F N`: `E s g = E_sch s (adelicHomeomorph⁻¹ g)` and likewise for `h`.

- Clause 1 is `eisensteinSeries_eq_schemeEisensteinSeries` (the comparison of the matrix sum
  with the scheme sum at `s λ₁`, for every `s`).
- Continuity and holomorphy pass through the homeomorphism.
- Left invariance uses `rational_rationalPointsEquiv`. For `x ∈ GL_N(F)`,
  `AdelicGL.rational F N x` is the image under `adelicHomeomorph` of the rational point
  `(rationalPointsEquiv F r t)⁻¹ x` of the scheme.

## Provenance

The statement is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
IV.1.8 (a), IV.1.9 (b)–(d) and IV.1.11 (a)–(b) (pp. 140–141). It is taken for the cuspidal datum
`(GL_(r+1) × GL_(t+1), π ⊗ (π')^∨)` and restricted to Shahidi's line of parameters
`s ↦ π ⊗ (π')^∨ ⊗ δ_P^(s/N)` (F. Shahidi, *On Certain L-Functions*, Amer. J. Math. 103 (1981),
§5, proof of Theorem 5.1, p. 351). The holomorphy on `Re s = 0` is stated conditionally on the
group-scheme form of Lapid's Proposition 6. The proof here derives clauses 1 and 2 from the
general statements of Bernstein–Lapid, Theorem 2.3 (1) and (6) (J. Amer. Math. Soc. 37 (2024),
p. 191), with the Corollary in §8.6. Mœglin–Waldspurger II.1.5 (pp. 85–86) gives the half-plane
of convergence.
