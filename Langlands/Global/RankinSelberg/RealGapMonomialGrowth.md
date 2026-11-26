# The real larger-gap equation for rotated split Gaussian monomial values

`RealGapMonomialGrowthStatement` (proved by `realGapMonomialGrowth`) assumes
`RealLocalUnequalCharacterGrowthAtRanks (t+1+q) t`. Let `cs`, `fs` be lists of real characters of lengths
`t+1+q+1` and `t+1`, `a ∈ ℝˣ`, `D`, `D'` quotient measure data at ranks `t` and `t+1+q`, `c` a real
character, `A` a uniform real Whittaker intertwiner of `cs.map character` at `−a` with a vector `u`, `B` one of
`fs.map character` at `a` with a vector `v`, a Gaussian monomial `gaussianPolynomial (monomial d c₀)` on
square matrices and a Schwartz function `φ` on columns. For
`W = rotatedValue t q a D' c (gaussianPolynomial (monomial d c₀)) (gaussianFactors (t+1) q d c₀ φ) (A u)`,
`ds = c :: cs` and `es = fs` (as block lists) it concludes
`HasRealPairNormalizedGrowth ds es (ds.map dualBlock) (es.map dualBlock) a √|a| _ (det(ds,−1)^(t+1) det(es,−1))`
for `realUnequalIntegral (rankLT t (q+1)) D W (B v)` and `realUnequalDualIntegral (rankLT t (q+1)) (−a) D W (B v)`.

## Proof

`gaussianPolynomial_eval_factors` splits the monomial test as `squareEval` of `gaussianFactors`. The dual
functions of `A u` and `B v` lie in the uniform models of `dualCharacterBlocks` (`realUniformWhittakerCharacterDual`).
With `κ` the normalized Haar measure of the compact orthogonal group (inversion invariant by
`isInvInvariant_of_compact`) and `η₁ = D.groupHaar`, `realGapExactRestriction` gives the ordinary and dual
restriction formulas with one positive constant `C`; `realGapOrdinaryMellin` and `realGapDualMellin` turn
them into Mellin identities with constants `Co = η_c(det w_(q+2)) · realAdjacentWeylSign c · C` and
`Cd = c((−1)^(t+1+q+1)) · realAdjacentWeylSign c⁻¹ · C`, and give the absolute moments. Here `η_c` is
`detCharacter c`, both Weyl signs are taken at index `t+1+q`, and the exponent `t+1+q+1` is the size of
the intermediate Godement matrix group `GL_(t+1+q+1)(ℝ)` on which `A u` is evaluated, that is the dimension
of the enlarged group `GL_(t+1+q+2)(ℝ)` minus one. With Jacquet's `n = t+1+q+2` and `n′ = t+1`, this is
the exponent `n − 1` of the central factor `μ_n(−1)^(n−1)` in (10.7), p. 75.

The two-scale identity required by the Library's `realGapGrowthFromSeparatedTheta` is checked at all scales
`b`, `c' > 0` with the half-rate weights: `realGapScaleComparison` gives
`η_{c⁻¹}(det w_(q+1)) ∫ F = (b c') ∫ Fd`, using the hypothesis for the smaller pair (after
`hasRealPairNormalizedGrowth_scale_congr` for `√|−a| = √|a|`), `integrable_ordinarySeparatedKernel`,
`realGapDualHaar` with `realGapDualSeparation`, and the finite orthogonal span of the leading tests from
`realGapLeadingCompact`. `phase_identity` shows `c(−1)^(t+1) · Co = Cd · η_{c⁻¹}(det w_(q+1))`, from
`det w_(q+2) = (−1)^(q+1) det w_(q+1)` and the equality of `c` and `c⁻¹` on elements of order two; after
rearrangement this is the phase calculation `μ_n(−1)^(n−1) μ_n(det w_(n−n′−1)) = μ_n(det w_(n−n′)) μ_n(−1)^(n′)` of p. 76. The reflection
factors factor as `c(−1)^(t+1)` times those of `cs × fs` and `[c] × fs` (`pairReflectionFactor_cons`, from
`realPairEpsilon_cons`), all for the epsilon parameter `a`.

This is the larger-gap step of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.3–10.4,
pp. 74–81, for split Gaussian monomial tests. Jacquet states that recurrence for rank differences greater
than two (§10, p. 68) and treats rank difference two separately in §9, pp. 61–68; the statement here
holds uniformly in `q`, and its case `q = 0` (from adjacent ranks to rank difference two) covers the
situation of §9.
