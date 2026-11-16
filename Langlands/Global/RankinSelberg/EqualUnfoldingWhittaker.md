# The mirabolic and Whittaker steps of the equal-rank unfolding

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
formalizes the second half of the unfolding in Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §2.3, printed p.210 (PDF p.213): "replace φ by its Fourier expansion and unfold
as before". The input is the integral of the kernel `φ φ' Φ(e_n ·) |det|^s` over
`P_n(F) \ GL_n(𝔸)`, `n = r + 1`, and the output is the Whittaker integral `Ψ(s; W, W', Φ)`.
The statements are abstract in the functions involved, so the same theorems serve the primal
integral (character `ψ`) and the dual one (character `ψ⁻¹`).

Notation: `equalKernel F f f' Φ s` is the kernel of `EqualUnfoldingKernel.md`. `ψ₀` is a
standard additive character. `genericCharacter F r ψ₀ (fun _ => 1)` is the generic character
`θ` of `N_n(𝔸)`. The hypotheses are:

- `hWθ`: `W(n x) = θ(n) W(x)` for `n ∈ N_n(𝔸)`;
- `hW'θ`: `W'(n x) = θ(n)⁻¹ W'(x)`;
- `hφ'Γ`: `φ'` is left `GL_n(F)`-invariant;
- `hW'`: `W'` is the `θ⁻¹`-Whittaker coefficient of `φ'`, i.e. `W'(x)` is the Library's
  `quotientMassNormalizer` times `∫_{n ∈ fd} φ'(n x) θ(n) dn`, over the chosen fundamental
  domain `unipotentFundamentalDomain` of `N_n(F)` in `N_n(𝔸)`;
- `hE`: the Fourier expansion `φ(g) = Σ_{γ ∈ N_r(F) \ GL_r(F)} W(diag(γ, 1) g)`, as a `HasSum`;
- `hG`: the kernel `W φ' Φ(e_n ·) |det|^s` is integrable over `N_n(F) \ GL_n(𝔸)`, evaluated at
  quotient representatives `q.out`, for the Library's `LeftCosetSpace.haarQuotientMeasure`.

## Lemmas

- `equalKernel_rational_unipotent_mul`: with `hWθ` and `hφ'Γ`, the kernel `W φ' …` is left
  `N_n(F)`-invariant, because `θ` is trivial on `N_n(F)` (Library `genericCharacter_rational`).
- `equalKernel_unipotent_mul`: with `hWθ` and `hW'θ`, the kernel `W W' …` is left
  `N_n(𝔸)`-invariant.
- `hasSum_equalKernel`: with `hE`, the kernel `φ φ' …` at `x` is the sum over
  `N_r(F) \ GL_r(F)` of the kernel `W φ' …` at `diag(γ, 1) x`. Here `φ'`, the last row and
  `|det|` are invariant under `diag(γ, 1) ∈ P_n(F)`.
- `setIntegral_unipotent_equalKernel`: with `hWθ` and `hW'`, averaging the kernel `W φ' …`
  over the fundamental domain of `N_n(F)` in `N_n(𝔸)` gives its Haar mass times the kernel
  `W W' …`. The mass cancels the normalizer by the Library's `quotientMassNormalizer_mul_haar`.

## Step III alone

`integrable_equalWhittakerIntegrand_of_kernel`: under `hφ'Γ`, `hWθ`, `hW'θ`, `hW'`, `hG` and
measurability, the Library's `equalWhittakerIntegrand F W W' Φ s` is integrable for
`whittakerQuotientMeasure`. The proof transfers `hG` to the fundamental domain of `N_n(F)`
(`integrable_out_iff`), averages with the Library's `setIntegral_eq_of_average`, and passes to
`N_n(𝔸) \ GL_n(𝔸)` with the Library's `integrable_and_integral_whittakerQuotient`. No Fourier
expansion is used.

## Steps II and III

`mirabolic_unfolding`: under all the hypotheses above, the kernel `φ φ' Φ(e_n ·) |det|^s` is
integrable on the chosen fundamental domain of `P_n(F)`. Its integral there equals the
Library's `equalWhittakerIntegral F W W' Φ s`, and the Whittaker integrand is integrable.

Proof. By `existsUnique_cornerAdelicPoint`, the union `⋃_γ diag(γ, 1) · D_P` of translates of
the fundamental domain `D_P` of `P_n(F)` is a fundamental domain of `N_n(F)`
(`existsUnique_mem_iUnion_smul`, `IsFundamentalDomain.mk'`). The integrability from `hG` moves
to this domain. The Library's `integrableOn_tsum_and_setIntegral_eq` then gives integrability
of the orbit sum on `D_P`, and the equality of its integral with the integral over the union.
By `hasSum_equalKernel` the orbit sum is the kernel `φ φ' …`. This is step II, the unfolding
of the sum over `N_r(F) \ GL_r(F)` against `P_n(F) \ GL_n(𝔸)`. Step III is the averaging over
`N_n(F) \ N_n(𝔸)` with `setIntegral_unipotent_equalKernel`, which turns `φ'` into `W'`,
followed by the passage to `N_n(𝔸) \ GL_n(𝔸)`.
