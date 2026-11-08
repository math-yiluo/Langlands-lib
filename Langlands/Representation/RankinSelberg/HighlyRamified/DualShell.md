# The dual integrand of the smeared test vector

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika 1985,
§4.4, printed pages 329–330: the computation of the right-hand side of (14), which they carry
out with the choices (16)–(18); here the internal Kirillov shell vector of `KirillovShell`
replaces their `W'`). The canonical topology, valuation and Borel structure of the p-adic field are
local instances.

- `dualWeightFourier F ψ ω ϖ c f T x`: the function `x ↦ S₂(rev x)`, where
  `S₂(ξ) = Σ_(z ∈ T) Φ₂(z) ψ(Σ_k z_k ξ_k)` for integral `ξ` and `0` otherwise, and `Φ₂` is
  `dualWeight ω ϖ c f` (the weight (18)).
- `twistedSmear F ψ η χ ω ϖ c f T f' g = χ(det g)⁻¹ ∫ S₂(rev x) f̃'(g ū_x) dx` over
  `rectangularMeasure η 1 (m+1)`. Here `f̃'` is the published `secondDualFunction ψ (m+1) f'`
  and `ū_x = lowerRow x`. It is the `χ⁻¹`-twisted smeared second dual function that appears as
  the `GL_(m+2)` vector in the functional equation for the pair `(σ̃ ⊗ χ⁻¹, τ)`.
- `determinant_weyl_inverseTranspose_rankInclusion`:
  `det(w ᵗdiag(B,1)⁻¹) = det(w) det(B)⁻¹`.
- `twistedSmear_at_dual`: under the hypotheses of `integral_dualWeight_fourier` (conductor
  `O`, `f ≥ 1`, `ω` trivial on `1 + 𝔭^f`, `ϖ^c O ⊆ 𝔭^f`, `T` representatives of the support
  of `Φ₂` modulo `O^(m+1)`),
  `twistedSmear(w ᵗdiag(B,1)⁻¹) = χ(det w)⁻¹ χ(det B) η(O)^(m+1) Φ₂(-rev B_last) f'(diag(B,1))`,
  where `B_last` is the last row of `B`. Proof: `smearedSecondDual_at_dual` and
  `inverseWhittaker_mul_inverseTranspose_lowerRow` reduce the integral to
  `f'(diag(B,1)) ∫ S₂(rev x) ψ(Σ_j B_(m,j) x_j) dx`, and `integral_dualWeight_fourier`
  evaluates it.
