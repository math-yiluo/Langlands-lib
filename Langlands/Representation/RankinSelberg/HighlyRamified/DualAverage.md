# Pairing finite algebraic averages of functions on a coset space

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, the averaged function `F_0` of formula (11) and the
replacement of `F_0` by `F` before (13), printed pages 328–329). Everything here is stated for
an arbitrary topological group `G`, subgroup `H` and quotient measure on `H \ G`; quotient
points are evaluated at the representatives `q.out`.

- `integral_pair_algebraicIntegral`: for a finite-image function `f : X → (G → ℂ)` with
  finite-measure support, `∫ Ξ(q.out) (∫ f dμ)(q.out) dμ_Q = ∫ (∫ Ξ(q.out) f(x)(q.out) dμ_Q) dμ(x)`
  whenever each inner product is integrable. The algebraic integral (published
  `AlgebraicIntegral.integral`) is a finite fiber sum, so this is linearity of the Bochner
  integral over finitely many terms; no Fubini theorem is used.
- `out_mk_eq`, `invariant_out_mk`: the representative of `H g` is `h g` with `h ∈ H`, so left
  `H`-invariant functions take the same value there.
- `integral_out_mul_right`: if right translations preserve `μ_Q` (the right-invariance clause of
  the published `IsCompatible`), then `∫ Φ(q.out k) dμ_Q = ∫ Φ(q.out) dμ_Q` for left invariant `Φ`.
- `rightTranslates`, `rightAverage`: for `F` right invariant under an open subgroup and a locally
  constant compactly supported weight `w`, the finite-image function `k ↦ w(k) F(· k)` and its
  algebraic integral `F̄ = ∫ w(k) F(· k) dk`; `rightAverage_apply` gives
  `F̄(g) = ∫ w(k) F(g k) dk` pointwise.
- `integral_pair_rightAverage`: if `Ξ(g k) = b(k) Ξ(g)` on the support of `w` and `Ξ F` is left
  invariant and integrable, then `∫ Ξ F̄ = (∫ w b⁻¹) ∫ Ξ F`.
- `inverseTranslates`, `inverseAverage`: the same for `k ↦ w(k) E(· k⁻¹)`.
- `integral_rightAverage_pair`: adjointness, `∫ E F̄ = ∫ F Ē` with `Ē = ∫ w(k) E(· k⁻¹) dk`, when
  the products `F(g k) E(g)` are left invariant and `F E(· k⁻¹)` is integrable for every `k`.

These replace the source's interchange of the `K_(r-2)(f)`-average with the quotient integral.
