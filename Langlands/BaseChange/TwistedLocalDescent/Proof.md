# Proof of the local descent of the twisted constant term

Module `Langlands.BaseChange.TwistedLocalDescent.Proof`.

- `indicator_mem_schwartzBruhat`: the restriction `1_S f` of a test function `f` to an open set
  `S` is a test function when the support of `f` is covered by `S` and an open set disjoint from
  `S`.
- `twistedLocalDescent : TwistedLocalDescentStatement` (the local form of the passage from (2) to
  (3) in Henniart–Lemaire, Mém. SMF 124 (2011), II.4.5).

## Proof

Given windows `Ω j ∋ d j`:

1. **Windows.** `exists_windows` gives open `Ω' j` with `d j ∈ Ω' j ⊆ Ω j` such that for all
   `x, x' ∈ Ω' j` and distinct blocks `i ≠ i'` the norm characteristic polynomials of `x'_{i'}`
   and `x_i` are coprime, and whose norm coefficients separate different `j`. Their
   `M(E)`-twisted saturations `S j` are open, pairwise disjoint (the norm coefficients are
   invariant under twisted conjugation because `σ^l = 1` for the cyclic algebra `E/F`) and
   contained in those of `Ω j`.
2. **Mass neighbourhoods.** Each `d j` is `x_j⁻¹ δ σ(x_j)` and `D_{G/M,σ}(d j) ≠ 0`
   (`twistedRelativeParabolicDiscriminant_ne_zero_of_cyclicNorm`, the norm of `d j` being the base
   change of the regular semisimple `m j`). `exists_nhds_integral_twistedOrbitalKernel` gives an
   open `V j ∋ δ` controlling the mass of the pieces supported near `d j`.
3. **Support.** By the classification (`exists_levi_twistedConj_of_parabolic`) and compactness
   (`exists_nhds_forall_proj_mem`) there is an open `U₁ ∋ δ` such that `k⁻¹ p σ(k) ∈ U₁`,
   `k ∈ K`, `p ∈ P` imply that the Levi part of `p` lies in `⋃ S j`.
4. Put `U₀ = U₁ ∩ ⋂ V j`. For `φ` supported in `U₀`, the normalized twisted constant term
   `φ^{P,σ}` (the Library's `normalizedTwistedParabolicConstantTerm E B σ φ`, evaluated by
   `normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup` with the given `μU`, `μK`)
   vanishes outside `⋃ S j` (if `φ^{P,σ}(x) ≠ 0`, some `k⁻¹ x u σ(k)` lies in `U₁`). The pieces
   are `ψ j = 1_{S j} φ^{P,σ}`: test functions (`indicator_mem_schwartzBruhat` with the other
   saturations), supported in the saturation of
   `Ω j`, summing to `φ^{P,σ}` (disjointness), and with
   `∫ ψ j = ∫_K Φ_j = |D_{G/M,σ}(d j)|^{-1/2} ∫ φ` by `integral_indicator_twistedConstantTerm` and
   step 2.

The route differs from Henniart–Lemaire, who pass to quotients by twisted centralizers and use
the Weyl integration formula; here the mass is computed directly through the parabolic, the
Iwahori factorization of a congruence subgroup and a change of variables through the twisted
conjugation chart at `d j`, whose Jacobian is `|det_F(σ − Ad(d j)⁻¹ | 𝔲̄)|`.
