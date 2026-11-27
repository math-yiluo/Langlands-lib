# The convergent cuspidal test expansion from its analytic inputs

Module `Langlands.Global.CuspidalTestExpansion.Reduction` (namespace `Langlands.Global`).

Notation: for the rational point `n` of the target, `[M(w, λ)φ]_{wλ}` denotes the selected
target-twisted intertwining integral `hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n φ λ`,
computed with the representative `n` of `w = [n]` (Bernstein–Lapid, *Meromorphic continuation of
Eisenstein series* (2024), §2.2, p. 191, where the target twist is part of the notation).

## Declarations

- `StandardParabolicFamily.leviPairingIntegrand_finsetSum`: the Levi pairing integrand of a
  finite sum of functions is the sum of their integrands.
- `StandardParabolicFamily.leviPairing_finsetSum_of_integrable`: the Levi pairing is additive over finite sums
  whose pairing integrands are integrable (`integral_finsetSum`).
- `convergentCuspidalTestExpansion_uniform_of_inputs`: from `ConstantTermAutomorphyStatement`,
  `AutomorphicExponentDecompositionStatement` and `LeviCuspFormRapidDecayStatement` it proves the
  conclusion of
  `ConvergentCuspidalTestExpansionStatement` (the scalar form of Bernstein–Lapid (6.20)) with two
  additions:
  - after the threshold `R` and the competing data, there is one degree bound `deg`, chosen
    before `λ`, such that every competing term satisfies
    `HasPolynomialOrbit J (data.label k λ) deg (terms k)`;
  - for every Levi cusp form `test` and every `g`, the pairing integrands of
    `constantTerm J (E(φ, λ))` and of `parabolicConstantTerm Q J ([M(w, λ)φ]_{wλ})` are integrable on
    `M_J(F) \ M_J(𝔸)^1`, as are those of the competing terms.
- `convergentCuspidalTestExpansion_of_inputs`: the same three inputs prove
  `ConvergentCuspidalTestExpansionStatement`. It forgets the additions, using
  `HasUnnormalizedExponent J λ f ↔ ∃ k, HasPolynomialOrbit J λ k f` (the two definitions have
  the same body).
- `convergentCuspidalTestExpansionReduction : ConvergentCuspidalTestExpansionReductionStatement`,
  which is `convergentCuspidalTestExpansion_of_inputs`.

## The proof of `convergentCuspidalTestExpansion_uniform_of_inputs`

Fix the data of the target: the family, `I`, `Q`, the rational point `n` with Weyl conjugation
`M_Q ≅ M_I`, `w = [n]` with `w(I) = Q`, the compact `K`, `rho`, `φ` automorphic along `I`, and
the index `J`. The integration identity `GeometricLemmaUnfoldingStatement` of the geometric
lemma, which several steps use, is the theorem `geometricLemmaUnfolding` (module
`EisensteinConstantTerm.GeometricLemmaUnfoldingProof`).

*Rank zero.* If `N = 0`, the closed embedding `rho` into `GL_0` makes `G(𝔸)` a single point
(`RepresentationGrowth.isClosedEmbedding_adelicMatrix`); then `G(F)` is trivial
(`rational_injective`), so is the relative Weyl group, and a Coxeter system on it has no simple
reflections, so there are no simple roots. Hence `J ≤ Q` and `Q = I`, `n = 1`, the Eisenstein
series is the single term `φ_λ` and the intertwining integral at `1` is `φ_λ`
(`IsIwasawaCompact.intertwiningIntegral_one_self`). Both tested terms agree, the competing
family is empty and `deg = 0`. Every pairing integrand is integrable: `M_J(𝔸)` is a point (the
closed embedding `fam.l J ≫ fam.p J`, `isClosedEmbedding_map`, injects it into `G(𝔸)`), so the
norm-one quotient is a point. Its Haar measure is locally finite, hence finite, and the integrand
is constant (`integrable_const`).

*Positive rank.* Let `0 < N`.

1. Bruhat data. `relativeWeylCoxeter` gives a Coxeter system on the relative Weyl group.
   `exists_standardBruhatRepresentatives` gives rational lifts of the minimal double coset
   representatives `v ∈ W_J \ W / W_I`, with the lift of `w` equal to `n`, forming double coset
   representatives of `P_J(F) \ G(F) / P_I(F)`; `standardBruhatPiece` gives for each `v` a Bruhat
   piece with source index `I_v` and target index `J_v ≤ J`.
2. The constant term formula. `eisensteinConstantTerm_of_convergence_of_unfolding` (with
   `eisensteinAbsoluteConvergence` and `geometricLemmaUnfolding`)
   gives `R₀` such that for regular `λ` the constant term along `U_J` of `E(φ, λ)` is
   `∑_v S_v`, where `S_v(y) = ∑_{γ ∈ P_{J_v}(F) \ P_J(F)} Pint_v(γ y)` and `Pint_v` is the piece
   integral (Bernstein–Lapid (6.17)). `eisensteinGlobalMajorant` gives `R₁` and, for regular `λ`,
   a summable majorant of degree `d`; take `R = max R₀ R₁`.
3. Pieces with proper target (`J_v < J`): the pairing of `S_v` with any cusp form on `M_J` is
   integrable and zero (`NestedLeviParabolic.properPiece_pairing`). Its hypotheses come from
   `pieceIntegral_properties` (continuity, `P_{J_v}(F)`-invariance), from
   `pieceIntegral_radical_invariant` with the automorphy of `C_{I_v} φ` given by the premise
   `ConstantTermAutomorphyStatement`, from the absolute bound `eisensteinBruhatAbsoluteBound`,
   and from the premise `LeviCuspFormRapidDecayStatement` at exponent `d`.
4. Pieces with full target (`J_v = J`): `S_v = Pint_v` (`fullPiece_series`). `Pint_v` is
   continuous, left `M_J(F)`-invariant and polynomially bounded, so its pairing with cusp forms is
   integrable (`weightedLeviPairingIntegrability`, with the rapid decay premise); the same holds
   for every positive split translate (`splitComponent_mem_leviPairingDomain`).
5. The selected piece. If `J ≤ Q`, the minimal representative `w` has full target
   (`selectedBruhatGeometry`), its lift is `n`, and `Pint_w` is the constant term along `U_J` of
   `[M(w, λ)φ]_{wλ}` (`selectedPiece_constantTerm`, using the Bruhat piece of `n` for the pair
   `(I, Q)`, which has source `I` and target `Q`). This is exactly the subtracted term
   `parabolicConstantTerm Q J ([M(w, λ)φ]_{wλ})`. If `J ≰ Q`, the subtracted term is `0`, and no
   full-target representative equals `w`.
6. Competing terms. For each full-target `v` other than the selected one, `fullPiece_expansion`
   is applied. By the premise `ConstantTermAutomorphyStatement` the full constant term
   `C_{I_v} φ` (not its cuspidal projection) is automorphic along `I_v`, and the premise
   `AutomorphicExponentDecompositionStatement` writes it as a finite sum
   `C_{I_v} φ = ∑_{ν ∈ s_v} comp_{v,ν}`, where `comp_{v,ν}` has unnormalized exponent `ν` along
   `I_v`; `s_v` is this finite set of unnormalized exponents of `C_{I_v} φ`. Together with an
   offset `offset_v`, a Weyl conjugation `c_v` and a projection `π_v`, all independent of `λ`,
   this gives
   for each `λ` a decomposition `Pint_v = ∑_{ν ∈ s_v} T_{v,ν}`, where `T_{v,ν}` is the
   intertwining integral of `comp_{v,ν}` and has unnormalized exponent
   `weylParameter (fam.l I_v) c_v π_v (ν + λ|) + offset_v` along `J` and lies in the span of the
   positive split translates of `Pint_v` (so its pairings with cusp forms are integrable). It
   also gives a degree bound `k_v`, independent of `λ`, for all `T_{v,ν}`: the exponent
   components of the fixed function `C_{I_v} φ` have fixed degrees, and the intertwining integral
   keeps the degree (`exists_offset_hasPolynomialOrbit_intertwiningIntegral`). Its proof also
   supplies `offset_v`, whose power at a point `x` of `𝔄_{P_J}` is the Haar factor of conjugation
   by `x` on `U_J(𝔸)` divided by that of its restriction to the closed adelic stabilizer
   `(U_J ∩ n_v U_{I_v} n_v⁻¹)(𝔸)`, where `n_v` is the rational lift of `v`. The degree bound
   of the target is `deg = max_v k_v` (`Finset.univ.sup`, with `HasPolynomialOrbit.mono`).
   Bernstein–Lapid obtain the sharper support by cuspidal exponents instead: they pass to
   cuspidal projections, using `(M(w, λ)φ)^cusp = M(w, λ)(φ^cusp)` ((6.9), §6.2, p. 202) in the
   proof of (6.17)–(6.20). The scalar target needs only the finite exponent set `s_v` of the
   full constant term, so the proof does not use cuspidal projections.
7. The data. The competing family `CompetingWeylExponents fam I J w` is indexed by the pairs
   `(v, ν)` (enumerated by `Fintype.equivFin`), with Weyl element `v`, linear part
   `weylParameter ∘ parameterRestrict`, and offset `weylParameter ν + offset_v`. The competing
   condition holds by step 5; positivity of `v(α)` for `α ∈ I` is the minimality of `v`
   (`minimalityLengthCriterion_proof` and the Coxeter realization); the ambient condition is
   `standardBruhatParameter`.
8. Integrability of the left-hand terms. The pairing integrand of `C_J E(φ, λ) = ∑_v S_v` is
   the sum of those of the `S_v` (`leviPairingIntegrand_finsetSum`), each integrable by steps 3
   and 4. The subtracted term is `Pint_w` when `J ≤ Q` (step 5), with integrable integrand by
   step 4, and `0` otherwise.
9. The identity. By linearity of the pairing on integrable functions
   (`leviPairing_finsetSum_of_integrable`), the pairing of the constant term of `E(φ, λ)` is the sum over `v` of
   the pairings of `S_v`; the proper pieces contribute `0`, the selected piece (if any) cancels
   the subtracted term, and each competing piece contributes `∑_ν` of the pairings of `T_{v,ν}`.
