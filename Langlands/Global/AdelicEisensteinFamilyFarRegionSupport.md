# Continued exponent support for finite families of inducing data

Module `Langlands.Global.AdelicEisensteinFamilyFarRegionSupport` contains the analytic core of
the far-region step of Bernstein–Lapid §8.6, for finite families of inducing forms in one
standard family `fam`.

## Auxiliary declarations

- `CompetingWeylExponents.sigma` concatenates finitely many lists of competing Weyl exponents
  (`CompetingWeylExponents`, module
  `Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement`) for the same `I`, `J` and
  selected Weyl element. Its labels are indexed by `Fin (∑ v, size v)` through
  `finSigmaFinEquiv`. `CompetingWeylExponents.sigma_label` identifies the label at the image of
  `⟨v, k⟩` with the `k`-th label of the `v`-th list.
- `leviPairing_sum_smul`: the norm-one Levi pairing against a fixed test is linear on finite
  combinations of functions whose pairings converge absolutely.
- `leviPairing_constantTerm_sum_of_automorphic`: for automorphic forms `f v` on `G(F) \ G(𝔸)` and a
  Levi cusp form with integrable weighted majorants, the test of `C_J (∑ v, c v · f v)` is
  `∑ v, c v` times the tests of the `C_J (f v)`. The forms are automorphic on the quotient for
  the top index (`isAutomorphicOn_top_iff`). Their constant terms have absolutely convergent
  tests by `constantTerm_mem_leviPairingDomain_of_le` (module
  `Langlands.Global.AdelicParabolicConstantTermTests`). Linearity is the Library's
  `leviPairing_constantTerm_sum_smul`.

## The theorem `exists_competingWeylExponents_continued_support_family`

The hypotheses are as follows.

- `ConvergentCuspidalTestExpansionStatement` holds.
- `(n, c, proj)` is a Weyl conjugation from `P_I` to `P_Q` with `w(I) ⊆ Q` and `w⁻¹(Q) ⊆ I`.
- `K` is in good position and Iwasawa for `P_I` and `P_Q`. The matrix embedding `rho` is closed
  of positive size. The Levi cusp forms along `J` have integrable weighted majorants.
- `φ v` (`v < p`) are automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)`.
- `Ev v : ℂᵐ → (G(𝔸) → ℂ)` are automorphic on `G(F) \ G(𝔸)` at every point of an open dense
  `U`, have meromorphic tests `s ↦ (C_J (Ev v s)(· g), ψ)` on `U`, and agree with `E(φ v, e s)`
  for regular `e s`.
- `b v` are meromorphic on an open dense `Db`.
- `ψ i` are automorphic on the quotient for `P_Q`, the constant terms `C_J (ψ i)` have cuspidal
  projections when `J ≤ Q`, and the coefficients `coeff i` are meromorphic on an open dense `Dc`.
- For regular `λ = e s`, `∑ v, b v s · M(w, λ)(φ v) = ∑ i, coeff i s · ψ i`.

The theorem gives competing Weyl data `data` for `(I, J, w)`. Fix a Levi cusp form `ψ` along
`J` and `s ∈ U ∩ Db ∩ Dc`, and consider the scalar function

`Φ s : g ↦ (C_J (∑ v, b v s · Ev v s)(· g), ψ) − (C_{Q,J}(∑ i, coeff i s · ψ i)_{wλ}(· g), ψ)`.

In every finite joint generalized eigendecomposition of `Φ s` for the positive split
component `𝔄_J`, every component vanishes whose character differs from all
`b ↦ b^{data.label j (e s)}`.

## Proof

For each `v`, `ConvergentCuspidalTestExpansionStatement` gives a threshold and competing data
`datav v`, and `exists_intertwiningIntegral_regular` (module
`Langlands.Global.AdelicStandardIntertwiningRegularity`) gives a threshold beyond which the
intertwining integral `I_v(λ)` of `φ v` is invariant under `U_Q(𝔸) M_Q(F)`, continuous and of
moderate growth. Put `data = sigma datav`. Let `W` be the part of `D = U ∩ Db ∩ Dc` where `e s`
exceeds all these thresholds and the agreement thresholds of the `Ev v` and of the intertwining
datum. `W` is open and nonempty.

1. **Meromorphy.** On `U`, the first test in `Φ s` equals `∑ v, b v s` times the tests of the
   `C_J (Ev v s)` (`leviPairing_constantTerm_sum_of_automorphic`). That sum is meromorphic on
   `D`. The second test is meromorphic on `Dc` by `eisensteinInducingPairingContinuation`. So
   every point evaluation of `Φ` is meromorphic on `D` (`IsMeromorphicOn.congr_domain`).
2. **Seed.** Fix `s ∈ W` and write `λ = e s`. By `intertwiningIntegral_eq_parameterTwist` and
   the hypothesis on the intertwining datum, the twisted inducing expression
   `(∑ i, coeff i s · ψ i)_{wλ}` equals `∑ v, b v s · I_v(λ)`. The constant term `C_J` is linear
   on these functions (`constantTerm_finset_sum_of_le`), and their constant terms have absolutely
   convergent tests (`constantTerm_mem_leviPairingDomain_of_le`). So the second test is
   `∑ v, b v s · (C_{Q,J} I_v(λ), ψ)`, and
   `Φ s = ∑ v, b v s · [(C_J E(φ v, λ), ψ) − (C_{Q,J} I_v(λ), ψ)]`. By (6.20) for `φ v`, the
   bracket is the sum of the tests of the competing terms of `datav v`. Each test lies in the
   joint generalized eigenspace of its label (`leviPairing_mem_jointGenEigenspace`), and so does
   its multiple by `b v s`. After reindexing by `finSigmaFinEquiv`, `Φ s` is a sum of
   eigenvectors for the characters of the labels of `data`.
3. **Continuation.** The characters `s ↦ b^{data.label j (e s)}` are entire
   (`differentiable_parameterPower_affine`). `meromorphicExponentSupport` (module
   `Langlands.Analysis.Meromorphic.ExponentSupport`) continues the support from `W` to `D`.

Step 2 is where the finite family needs more than the single inducing form. The test of
`C_{Q,J}` of the combination splits into the tests of its summands only if every summand has an
absolutely convergent test. The regularity of intertwining integrals supplies this.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math.
Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §8.6,
p. 225, with Lemma 6.8 and (6.20), §6.6–6.10, pp. 206–209. Bernstein–Lapid continue each competing
term of (6.18) by continuing the intertwining operators `M(v, λ)`. This module instead continues
the support of their sum, and uses (6.20) only in the region of convergence.
