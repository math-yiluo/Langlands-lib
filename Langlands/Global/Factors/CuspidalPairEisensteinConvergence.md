# Normal convergence of the cuspidal-pair Eisenstein series

Module `Langlands.Global.Factors.CuspidalPairEisensteinConvergence` states and proves
`Langlands.Global.CuspidalPairEisenstein.CuspidalPairEisensteinNormalConvergenceStatement.{u}`.

## The statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`, `r t : ℕ`,
`N = r + t + 2`, `T : CuspidalOperatorRealization F r`, `T' : CuspidalOperatorRealization F t`,
and `φ` with `IsSection T T' φ` (module `Langlands.Global.Factors.CuspidalPairEisensteinSeries`).
Then there is a real `σ` with the following property. For every compact `C ⊆ GL_N(𝔸)` and every
compact `Λ ⊆ ℂ` with `σ < Re s` for all `s ∈ Λ`, there is a summable `b` on the coset space
`Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F))` of `P(F) \ GL_N(F)` such that

  `‖φ(γ_c g) · heightPower F r t s (γ_c g)‖ ≤ b c`

for every coset `c`, every `g ∈ C` and every `s ∈ Λ`, where `γ_c` is the principal adelic matrix of
the chosen representative `Quotient.out c`. These are exactly the terms of the unconditional sum
`eisensteinSeries F φ s g`. No unitarity of the central characters is assumed. The theorem
`cuspidalPairEisensteinNormalConvergence` proves the statement.

In particular the terms are absolutely summable for `Re s > σ`, so on that half-plane
`eisensteinSeries F φ s g` is the sum of an absolutely convergent series, locally uniformly in
`(s, g)`.

## Implemented proof

- `matrixTerm_parabolicCosetsEquiv`: for a scheme coset `c` and an adelic point `g` of the scheme
  `GL_N`, the matrix term at the representative of `parabolicCosetsEquiv F r t c` and the adelic
  matrix of `g` is the scheme term `hK.eisensteinTerm (φ ∘ adelicHomeomorph F N) (s • λ₁) g c`.
  The proof is the termwise step of `eisensteinSeries_eq_schemeEisensteinSeries` (module
  `Langlands.Global.Factors.CuspidalPairSchemeSeries`): the matrix terms are left invariant under
  `B.parabolic F` (`isSection_rational_mul`, `heightPower_rational_mul`), the two representatives
  lie in the same right coset, and `heightPower_eq_schemeHeightPower` compares the twists.
- `exists_summable_eisensteinTerm_bound`: apply the Library theorem
  `eisensteinAbsoluteConvergence` (`EisensteinAbsoluteConvergenceStatement`) to the scheme `GL_N`,
  the block parabolic with its block-unipotent radical and block Levi, the presentation
  `blockRootData`, the standard maximal compact subgroup (`isIwasawaCompact_blockParabolic`,
  `standardCompactPoints_isMaximalCompact`), the standard embedding and the transported section,
  which is automorphic on the parabolic quotient by `isAutomorphicFunctionOn_of_isSection`. This
  gives a threshold `R`. `exists_isRegularParameter_lineParameter` (module
  `Langlands.Global.Factors.CuspidalPairLineRegularity`) gives `σ` such that `s • λ₁` is
  `R`-regular for `Re s > σ`. In the coordinates `parameterCoordinates` of `X^*(P) ⊗ ℂ`, the set
  `{s • e⁻¹(λ₁) : s ∈ Λ}` is compact, and the image of `C` under the inverse of `adelicHomeomorph`
  is compact. The resulting summable bound on the scheme cosets is transported to the matrix cosets
  along `parabolicCosetsEquiv`.

## Provenance

This is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), II.1.5,
Proposition, pp. 85–86 (normal convergence of Eisenstein series for parameters in a translate of
the positive chamber, uniformly on compact sets), for the cuspidal datum
`(GL_(r+1) × GL_(t+1), π ⊗ (π')^∨)` and restricted to Shahidi's line of parameters
(F. Shahidi, *On Certain L-Functions*, Amer. J. Math. 103 (1981), §5, proof of Theorem 5.1,
p. 351). The proof here deduces it from the Library's general convergence theorem; it does not
give an explicit value of `σ`.
