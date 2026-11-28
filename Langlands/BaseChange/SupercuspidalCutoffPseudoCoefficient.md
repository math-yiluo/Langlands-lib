# Pseudo-coefficients of supercuspidal representations with vanishing constant terms

The module `Langlands.BaseChange.SupercuspidalCutoffPseudoCoefficient` (namespace
`Langlands.BaseChange.SupercuspidalCutoff`) proves:

**`exists_cuspForm_pseudoCoefficient`.** Let `F` be a nonarchimedean local field
(`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, any characteristic),
`0 < n`, `GL_n(F)` Hausdorff, locally compact and totally disconnected with a Borel σ-algebra,
`μ` a Haar measure, and `π` an irreducible supercuspidal representation of `GL_n(F)` on
`V : Type uV` (`GeneralLinear.IsSupercuspidal π`, `π.IsIrreducible`) with
`HasCentralCharacterRep π χ`. Then there is `f : SchwartzBruhat (GeneralLinear n F)` with

1. `HasVanishingConstantTerms f` (module `Langlands.BaseChange.CuspForm`);
2. `Character.distribution μ π hπ.1 f = 1`;
3. `Character.distribution μ ρ hρ f = 0` for every representation `ρ` on `W : Type uW` with
   `hρ : IsAdmissible ρ`, `ρ.IsIrreducible`, `HasCentralCharacterRep ρ χ` and
   `IsEmpty (ρ.Equiv π)`.

## The Schur constant is nonzero

By `exists_integratedAction_cutoff_self` (module `Langlands.BaseChange.SupercuspidalCutoffTraces`)
the cut-off coefficients `f_x = cutoff π ℓ hn hπ hℓ x` satisfy `π(f_x) w = c(w) x`, so
`ℓ(π(f_x) x) = c(x) ℓ(x)`, while `ℓ(π(f_x) x) = ∫ f_x(g) ℓ(π(g) x) dμ(g)`
(`Hecke.integratedAction_dual`). It suffices to find a smooth `ℓ` and a vector `s` for which
this integral is nonzero. The module builds `ℓ` from a positive Hermitian form.

- *Weight.* `weightBase χ = r = (‖χ(z)‖²)^{1/n}`, where `z` is the scalar uniformizer
  (`centralUniformizerCenter`), and `weight χ g = r^{ord det g}`. It is positive
  (`weight_pos`), multiplicative (`weight_mul`), equal to `1` where `ord det = 0`
  (`weight_of_detOrd_eq_zero`), locally constant (`isLocallyConstant_weight`), and
  `weight χ (z g) = ‖χ(z)‖² weight χ g` (`weight_centralUniformizer_mul`, from
  `r^n = ‖χ(z)‖²`).
- *Form.* For a smooth linear form `ℓ₀`,
  `formIntegrand π ℓ₀ χ x y g = ℓ₀(π(g⁻¹) x) · conj(ℓ₀(π(g⁻¹) y)) · r^{ord det g}` and
  `form π ℓ₀ χ μ x y = ∫ 1_{0 ≤ ord det g < n} formIntegrand π ℓ₀ χ x y g dμ(g)`.
  The integrand is invariant under left multiplication by `z` (`formIntegrand_central`: the
  factor `|χ(z⁻¹)|² ‖χ(z)‖²` is `1`) and integrable on level sets and on the window.
- `form_rho` (quasi-invariance): `B(π(h) x, π(h) y) = r^{ord det h} B(x, y)`, since
  `formIntegrand (π h x) (π h y) g = r^{ord det h} formIntegrand x y (h⁻¹ g)` and the window
  integral is invariant under left translation of `z`-periodic functions
  (`PeriodicWindow.integral_window_comp_mul_left`).
- `form_swap`: `B(y, x) = conj B(x, y)`; `form_add_left`, `form_smul_left`: `B` is linear in its
  first argument.
- `form_self`, `integral_selfDensity_pos`: `B(s, s)` is the real integral of the density
  `selfDensity` (`1_{window}(g) ‖ℓ₀(π(g⁻¹) s)‖² r^{ord det g}`), which is continuous, compactly
  supported, nonnegative, and nonzero at `g = 1` when `ℓ₀(s) ≠ 0`; Haar measure charges nonempty
  open sets (`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`), so `B(s, s) > 0`.
- `formDual` is the linear form `ℓ = B(·, s)`. `isSmoothVector_formDual`: `ℓ` is fixed by the
  contragredient action of the open subgroup of elements of `ker |det|` fixing `s`, by
  quasi-invariance.
- `form_rho_inv_self`: `B(π(g⁻¹) s, s) = r^{-ord det g} conj B(π(g) s, s)`, from quasi-invariance
  at `h = g` and Hermitian symmetry.
- `integral_cutoff_formDual_ne_zero`: for `ℓ = B(·, s)` with `ℓ₀(s) ≠ 0`,
  `f_s(g) ℓ(π(g) s) = 1_{window}(g) r^{-ord det g} ‖B(π(g) s, s)‖²` (the density
  `crossDensity`), a continuous, compactly supported, nonnegative function with value
  `B(s, s)² > 0` at `g = 1`; so `∫ f_s(g) ℓ(π(g) s) dμ(g) > 0`.

## Proof of `exists_cuspForm_pseudoCoefficient`

`V` is nontrivial because `π` is irreducible. Choose `s ≠ 0` and a smooth `ℓ₀` with
`ℓ₀(s) ≠ 0` (the Library's `CompactCoefficientSemisimplicity.exists_smooth_dual_separating`,
module `Langlands.Representation.CompactCoefficient.SemisimplicityProof`), and put
`ℓ = B(·, s)`. With `c` from `exists_integratedAction_cutoff_self`, `c(s) ℓ(s)` is the nonzero
integral above, so `c(s) ≠ 0`. The function `f = c(s)⁻¹ f_s` has vanishing constant terms
(`hasVanishingConstantTerms_cutoff` and `HasVanishingConstantTerms.const_mul`), trace
`c(s)⁻¹ c(s) = 1` on `π` (`distribution_cutoff_self`), and trace `0` on every `ρ` as in 3
(`distribution_cutoff_eq_zero`).

## Provenance

The proposition is the cusp-form part of the Library's
`SupercuspidalEllipticPseudoCoefficientStatement` (its Markdown, steps 1–3), whose sources are
Kazhdan, *Cuspidal geometry of p-adic groups* (1986), source ID
`kazhdan-1986-cuspidal-geometry`, §5, Proposition 3 and its proof (printed p. 28), and
Arthur–Clozel (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, Corollary 2.10
(printed p. 18). In the proof of Kazhdan's Proposition 3, `π` is square integrable, the test
function is `d_π⁻¹ f_π` modulo `I(G)`, where `f_π(g) = (π(g) v, v)` is the raw coefficient of a
unit vector `v` and `d_π` the formal dimension, and it is paired with representations through
`⟨π', h⟩ = Tr π'(h*)`, `h*(g) = h(g⁻¹)` (§1.2, printed p. 8). The normalization here is
different and does not assume unitarity: the test function is `c(s)⁻¹ f_s`, where `f_s` is the
cut-off inverse-argument coefficient and `c(s)` the Schur constant, which is the trace
`tr π(f_s)`; its nonvanishing follows from the positive density `crossDensity`, built from the
Hermitian form `B` with the weight `r^{ord det}` compensating a non-unitary central character.
Its value is not identified with a formal degree.
