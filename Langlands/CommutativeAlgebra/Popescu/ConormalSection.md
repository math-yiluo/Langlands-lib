# A section of the conormal sequence after inverting a smooth element

Let `φ : R[x_1, …, x_n] → B` be surjective with kernel `I = (f_1, …, f_m)`. Let `h` be a
polynomial whose image `a = φ(h)` has `B_a` formally smooth over `R`. In this situation the
conormal map `(I/I²)_a → ⊕_i B_a dx_i` has a left inverse (Stacks Project, *Smoothing ring
maps*, `smoothing.pdf`: proof of Lemma 2.2, tag 07C6, printed p. 3, "(I/I²)_a → ⊕ A_a dx_i is a
split injection"; proof of Lemma 3.7(e), tag 07EZ, printed p. 9, where the sequence
`0 → (I/I²)_a → ⊕ A_a dx_i → Ω_{A_a/R} → 0` is split exact). Stacks deduces this from the
definition of smooth ring maps through the naive cotangent complex. Here it is proved from
formal smoothness of `B_a` (lifting along a square-zero extension), and stated concretely in
terms of polynomials, without using Kähler differentials. Everything is in namespace
`SymRetract`.

## Statements

- `aeval_add_of_sqZero`: first-order Taylor expansion. If the elements `δ_i` multiply to zero
  in pairs, then `p(t + δ) = p(t) + Σ_i (∂p/∂x_i)(t) · δ_i`.
- `locKer φ h`: the ideal `I_h = I · R[x]_h` of `R[x]_h = Localization.Away h`.
- `exists_conormal_section_loc`: there are `c_il ∈ R[x]_h` such that, for every `k`,
  `f_k + Σ_i (∂f_k/∂x_i) · Σ_l c_il f_l ∈ I_h²`.
- `exists_conormal_section`: there are `t` and a polynomial matrix `P` such that, for every
  `k`, `h^t f_k − Σ_l (Σ_i ∂f_k/∂x_i · P_il) f_l ∈ I²`.

## Proof of `exists_conormal_section_loc`

1. Let `q : R[x]_h/I_h² → R[x]_h/I_h` be the projection. It is surjective, and its kernel
   lies in `I_h/I_h²`, which squares to zero.
2. The map `B → R[x]_h/I_h` induced by `x_i ↦ x_i` (`AlgHom.liftOfSurjective`) sends `a` to
   a unit. So it extends to `g : B_a → R[x]_h/I_h`.
3. Since `B_a` is formally smooth, `g` lifts along `q` to `s : B_a → R[x]_h/I_h²`
   (`Algebra.FormallySmooth.liftOfSurjective`).
4. Put `θ_i = s(x_i) − x_i`. These lie in the square-zero ideal `I_h/I_h²`.
5. For `f ∈ I`, the image of `f` in `B_a` is `0`, and `s` is an algebra map. Taylor expansion
   then gives `0 = s(f(x)) = f(x + θ) = f + Σ_i (∂f/∂x_i) θ_i` in `R[x]_h/I_h²`.
6. Writing `θ_i = Σ_l c_il f_l` (`Ideal.mem_span_range_iff_exists_fun`) gives the claim.

## Proof of `exists_conormal_section`

Clear the denominators of the `c_il` with a common power `h^{t₀}`
(`IsLocalization.exist_integer_multiples`). Then clear the denominator in each membership in
`I_h² = (I²)_h` with a power `h^{t₁(k)}` (`IsLocalization.algebraMap_mem_map_algebraMap_iff`).
Finally take `t = Σ_k t₁(k) + t₀` and `P_il = −h^{Σ t₁} p_il`.

## Status

`exists_conormal_section` runs with `maxHeartbeats` raised to `400000`. The module imports only
Mathlib and uses only the standard axioms.
