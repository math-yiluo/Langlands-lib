# Compact averages of modular-covariant functions

Author: Worker 235.

This module proves an abstract compact averaging theorem in
`Langlands.ModularCompactAverage`, with three small facts about Mathlib's
modular character `MeasureTheory.Measure.modularCharacter`. It is a helper for
`Langlands.Representation.Induction.CompactScalarProof`, which applies it to
standard block parabolics of `GL_n`. It defines nothing; every declaration is
a theorem.

## Provenance

The content is derived. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups* (draft May 1, 1995, source
`casselman-1995-admissible-representations`), proves Theorem 2.4.2 (p. 27)
with the projection `(P_δ f)(g) = ∫_H δ_H(h)⁻¹ f(hg) d_r h` and the invariant
functional `I_δ` characterized by `∫_G f = I_δ(P_δ f)`. In the proof of
Proposition 3.1.3 (pp. 32–33) he identifies `I_δ` with the compact average
`f ↦ ∫_K f(k) dk`. That identification is what makes the compact average
invariant under right translation. The theorem here states this invariance
directly for an abstract group. Its Lean proof does not follow Casselman's
route: it builds no functional on `P \ G` and no quotient measure. It is a
direct double-integral argument on `G × P`, described below.

## Conventions

Mathlib defines `modularCharacter : H →* ℝ≥0` for a locally compact group
`H` as the scalar factor of `map (· * q) haar` against `haar`. The first
theorem below shows that every left Haar measure `μ` on a second countable `H`
satisfies `map (· * q) μ = modularCharacter q • μ`. So for measurable `E`,
`μ (E q⁻¹) = modularCharacter q * μ E`.

## Statements

Section `Character`: `H` is a second countable, locally compact topological
group.

- `map_mul_right_eq_modularCharacter_smul μ q`: for a Haar measure `μ` on `H`
  with its Borel structure, `map (· * q) μ = modularCharacter q • μ`. Proof:
  `modularCharacterFun_eq_haarScalarFactor` together with uniqueness of
  left-invariant measures, `isMulLeftInvariant_eq_smul`.
- `modularCharacter_eq_one_of_mem U hUo hUc hu`: the modular character is `1`
  on every compact open subgroup `U`. Proof: right translation by `u ∈ U` fixes
  `U`, so `μ U = modularCharacter u * μ U` with `0 < μ U < ∞`, and
  `ENNReal.mul_eq_right` cancels.
- `measure_preimage_conj μ z hS`: for a measurable set `S`, the set
  `{p | z⁻¹ p z ∈ S}` has measure `modularCharacter z * μ S`. Proof: left
  invariance, then the first theorem.

Section `Average`: `G` is a second countable, locally compact topological
group with its Borel structure.

- `setIntegral_mul_right_eq μ P hP K hKo hKc hPK φ hφ hcov g`. Suppose `μ` is
  a Haar measure on `G` that is also right invariant, `P` is a closed subgroup
  with `[LocallyCompactSpace P]`, and `K` is a compact open subgroup with
  `G = P K` (`hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q * k`). Suppose `φ : G → ℂ`
  is continuous and satisfies `φ (q * x) = modularCharacter q * φ x` for every
  `q : P`, where `modularCharacter` is the modular character of `P`, coerced
  to `ℂ`. Then for every `g : G`,

  ```text
  ∫ x in K, φ (x * g) ∂μ = ∫ x in K, φ x ∂μ.
  ```

## Proof of the averaging theorem

Give `P` its Borel structure and a Haar measure `ν`. `P` is second countable
as a subspace. Write `Δ` for the modular character of `P` coerced to `ℂ`, and
`χ` for the indicator of `K`. `χ` is continuous because `K` is clopen. Let
`C = P ∩ K`, viewed as a subset of `P`. It is open, it is compact because
`P` is closed, and `0 < ν C < ∞`. Since `C` is a compact open subgroup of `P`,
`modularCharacter_eq_one_of_mem` gives `Δ = 1` on `C`.

Two inner integrals over `P` are constant:

1. `hinner₁`: for every `y`, `∫_P χ(p⁻¹ y g⁻¹) dν(p) = ν.real C`. Factor
   `y g⁻¹ = q k` with `q ∈ P`, `k ∈ K`. Then `p⁻¹ y g⁻¹ ∈ K` exactly when
   `q⁻¹ p ∈ K`, so the integrand is the indicator of the translate `q C`.
   Left invariance (`measure_preimage_mul`) gives its mass.
2. `hinner₂`: for every `z`, `∫_P Δ(p) χ(p z) dν(p) = ν.real C`. Factor
   `z = q k`. Then the integrand is `f(p q)`, where `f` is the indicator of
   `C` times `r ↦ Δ(r q⁻¹)`. Since `Δ = 1` on `C`, `f` is the constant `Δ(q⁻¹)`
   on `C`. The substitution `p ↦ p q` uses `integral_map_equiv` and
   `map (· * q) ν = modularCharacter q • ν`. The result is
   `Δ(q) Δ(q⁻¹) ν.real C = ν.real C`.

Both sides of the claim become integrals over `G`. The right side is
`∫_G χ(y) φ(y) dμ`, by `integral_indicator`. The left side is
`∫_G χ(y g⁻¹) φ(y) dμ`: substitute `y = x g`, using right invariance of `μ`
(`integral_mul_right_eq_self`). This is the only use of right invariance.

The proof compares two orders of integration twice. Let `S = K g⁻¹ K`, the
compact image of `K × K` under `(a, b) ↦ a g⁻¹ b`. Its preimage `P ∩ S` in `P`
is compact.

- `F₁(y, p) = φ(y) χ(y) χ(p⁻¹ y g⁻¹)` on `G × P` is continuous. It vanishes
  outside `K × (P ∩ S)`: if `y` and `p⁻¹ y g⁻¹` lie in `K`, then
  `p = y g⁻¹ (p⁻¹ y g⁻¹)⁻¹ ∈ S`. So it is integrable for `μ.prod ν`. By
  `hinner₁`, integrating over `P` first gives `ν.real C · ∫_G χ φ dμ`.
- After the swap (`integral_integral_swap`), substitute `y = p z` in the inner
  `G`-integral, using left invariance (`integral_mul_left_eq_self`). Then
  `F₁(p z, p) = F₂(p, z) = φ(p z) χ(p z) χ(z g⁻¹)`.
- `F₂` on `P × G` is continuous. It vanishes outside `(P ∩ S) × K g`, so it
  is integrable for `ν.prod μ`. Swap again. By the covariance hypothesis,
  `F₂(p, z) = (χ(z g⁻¹) φ(z)) · (Δ(p) χ(p z))`. By `hinner₂`, the `P`-integral
  is `ν.real C · χ(z g⁻¹) φ(z)`, so the total is
  `ν.real C · ∫_G χ(y g⁻¹) φ(y) dμ`.

Hence `ν.real C · RHS = ν.real C · LHS`. Since `ν.real C ≠ 0`, cancellation
gives the identity.

## Scope

The theorem needs `G` to be unimodular in the form of a right-invariant Haar
measure `μ`. It uses only continuity of `φ`, not local constancy. It does not
mention block parabolics, Levi decompositions or any particular modulus
formula. Identifying `modularCharacter` of a block parabolic with the block
modulus is done in `Langlands.Group.GL.ParabolicModularCharacter`.
