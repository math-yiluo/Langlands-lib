# The mass of the twisted orbital kernel over a local field

Module `Langlands.BaseChange.TwistedLocalDescent.MassLocal`.

- `twistedConj_mem_saturation_of_mem`: twisted conjugacy saturations are stable under twisted
  conjugation.
- `iwasawa_parabolicHaar`: with the Haar normalizations of Henniart–Lemaire (2011), II.4.5
  (`μG(K) = μM(M(𝒪)) = μU(U ∩ K) = 1`, `μK` a probability measure),
  `μG = (μP × μK).map (p, k ↦ p k)` for `μP = parabolicHaar B μM μU` (`dp = dm du`); this is
  `TwistedVanDijk.iwasawa_measure_eq` regrouped.
- `exists_radius_subset`: every neighbourhood of `1` in `GL_n(E)` contains `{g : ‖g − 1‖ < ε}`
  for some `ε > 0`.
- `exists_nhds_integral_twistedOrbitalKernel` (**local mass**): let `E/F` be a cyclic algebra of
  group `⟨σ⟩` of order `l` over nonarchimedean local fields, the Haar measures normalized as
  above, `Ω ⊆ M(E)` an open window such that for all `x, x' ∈ Ω` and distinct blocks
  `i ≠ i'` the norm characteristic polynomials of `x'_{i'}` and `x_i` are coprime (the windows of
  `exists_windows`), `d ∈ Ω` with `D_{G/M,σ}(d) ≠ 0`, and `x ∈ GL_n(E)`. There is an open
  neighbourhood `V` of `x d σ(x)⁻¹` such that for every test function `φ` supported in `V`,

  `∫_K Φ(k) dk = |D_{G/M,σ}(d)|_F^{-1/2} ∫_G φ`,

  where `Φ(k) = ∫_P 1_S(p_M) δ_P(p)^{1/2} φ(k⁻¹ p σ(k)) dp` and `S` is the `M(E)`-twisted
  conjugacy saturation of `Ω`.

  Proof: the local norm of `E` makes `σ` isometric (`norm_algEquiv_eq`). With `A` the
  automorphism `chartLinearEquiv`, `C` a bound for `A⁻¹` and `κ = max(‖d⁻¹‖‖d‖, 1)`, choose
  `r ∈ (0, 1)` with `C κ r < 1`, a congruence subgroup `U` of radius `r`, and `U` so small that
  `d · (P ∩ U)` has Levi parts in `Ω`; then `s ≤ r` with `B(0, s) ⊆ A(B(0, r))`, and
  `V = x d {g : ‖g − 1‖ < s} σ(x)⁻¹`. The hypotheses of `integral_twistedOrbitalKernel_eq_mass`
  hold: rigidity is `mem_parabolic_of_twistedConj`, `δ_P^{1/2}` is trivial on the compact group
  `P ∩ U`, the level of `φ` gives the bi-invariance, and the mass identity gives
  `δ_P(d)^{1/2} |det_F A|⁻¹ ∫ φ`, which is the weight by
  `sqrt_leviModulus_mul_inv_det_chartLinear`.
