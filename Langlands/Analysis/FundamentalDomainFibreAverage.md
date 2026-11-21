# Averaging over a normalized subgroup preserves quotient integrals

Module `Langlands.Analysis.FundamentalDomainFibreAverage`, namespace
`Langlands.Analysis.FibreAverage`.

## Statement

`FundamentalDomainFibreAverageStatement` (universes `u`, `v`) and its proof
`fundamentalDomainFibreAverage`. The data and hypotheses are as follows.

- `H` is a group with a measurable structure for which multiplication (`MeasurableMul₂`) and
  inversion are measurable. `μ` is a left-invariant s-finite measure on `H`.
- `Λ ≤ H` is a countable subgroup. `D ⊆ H` is a measurable **strict** fundamental domain for
  left multiplication by `Λ`: for every `x` there is exactly one `l ∈ Λ` with `l x ∈ D`.
- `j : V →* H` is an injective measurable homomorphism from a group `V` with the same
  measurability assumptions. `Γ ≤ V` is a subgroup with `j(Γ) ⊆ Λ` (it may be smaller than
  `j⁻¹ Λ`).
- `Λ` normalizes `j(V)`. This is given by maps `cj l : V → V` with
  `j (cj l w) = l · j w · l⁻¹`. Every `cj l` preserves `ν` and maps `Γ` into `Γ`.
- `ν` is an s-finite measure on `V` that is left-invariant and invariant under inversion.
- `C ⊆ V` is a measurable fundamental domain (in Mathlib's almost-everywhere sense) for left
  multiplication by `Γ` on `(V, ν)`.

Then for every measurable `F : H → [0, ∞]` with `F (l x) = F x` for `l ∈ Λ`,

`∫_D ∫_C F (j w · g) dν(w) dμ(g) = ν(C) · ∫_D F dμ`.

The module also exports `setLIntegral_fibreAverage` (the same theorem with section variables),
`tsum_lintegral_indicator_eq` (the fibre-counting identity below),
`tsum_eq_tsum_of_orbit_sums` (an orbit reindexing lemma for `[0, ∞]`-valued sums) and
`tsum_indicator_mul_eq_one`.

## Role in Bernstein–Lapid §7.3

Take `H = G(𝔸)`, `Λ = P₀(F)`, `V = U_P(𝔸)` for the unipotent radical of a standard parabolic
`P`, and `Γ = U_P(F)`. Then `j(Γ) ⊆ Λ`, and `P₀(F)` normalizes `U_P(F)` and `U_P(𝔸)`. Then `ν(C)⁻¹ ∫_C F (j w · g) dν(w)` is the constant term `CT_P F (g)`
(Bernstein–Lapid, J. Amer. Math. Soc. 37 (2024), §7.3, p.214), with `U_P(F) \ U_P(𝔸)`
normalized to mass one. The theorem says `∫_{P₀(F)\G(𝔸)} CT_P F = ∫_{P₀(F)\G(𝔸)} F`
for nonnegative `F`. This is the measure-theoretic input for BL's statement that `CT_P` is the
orthogonal projection of a weighted `L²` space onto the functions that factor through
`P₀(F) U_P(𝔸) \ G(𝔸)`. The present module proves it without constructing a quotient measure on
`P₀(F) U_P(𝔸) \ G(𝔸)`. The adelic instantiation and the operator consequences are not part of
this module. The provenance is derived: BL use the fibration `β_P` and the formula without
proof; the argument below is a direct proof of that formula.

## Proof

1. *Unfolding.* For fixed `w`, left invariance gives `∫_D F (j w · g) dμ = ∫_H 1_D((j w)⁻¹ h) F(h) dμ`.
   Unfold over the fundamental domain `D` (`IsFundamentalDomain.lintegral_eq_tsum''`) and use
   the `Λ`-invariance of `F`. This gives
   `∫_D F(g) · N_w(g) dμ`, with `N_w(g) = ∑_{l ∈ Λ} 1_D((j w)⁻¹ l g)`. Tonelli
   (`lintegral_lintegral_swap`, `lintegral_tsum`) reduces the theorem to
   `∑_{l ∈ Λ} ∫_C 1_D((j w)⁻¹ l g) dν(w) = ν(C)` for every `g` (`tsum_lintegral_indicator_eq`).
2. *The comparison family.* Since `D` is strict, `∑_l 1_D(l x) = 1` for every `x`
   (`tsum_indicator_mul_eq_one`). Applied at `x = j w · g` and integrated over `C`,
   this gives `ν(C) = ∑_{l} ∫_C 1_D(l · j w · g) dν(w)`.
3. *Orbit sums.* `Γ` acts freely on `Λ` by `γ · l = j γ · l`. Both families have the same sum
   over each orbit, namely `A(r) = ∫_V 1_D(j x · r · g) dν(x)`:
   - first family (`tsum_orbit_left`): `(j w)⁻¹ j γ = j((γ⁻¹ w)⁻¹)`; the translates `γ⁻¹ C`
     tile `V` (`IsFundamentalDomain.lintegral_eq_tsum'`); then inversion invariance of `ν`.
   - second family (`tsum_orbit_right`): `r · j w = j(cj r w) · r`. The substitution `x = cj r w`
     preserves `ν`, and `cj r⁻¹ ⁻¹' C` is again a fundamental domain of `Γ`
     (`IsFundamentalDomain.preimage_of_equiv`, with `cj r` permuting `Γ`). Its translates tile `V`.
4. *Reindexing* (`tsum_eq_tsum_of_orbit_sums`). Choose one point in each `Γ`-orbit of `Λ` by
   `Quotient.out` on `MulAction.orbitRel`. Its indicator `κ` has `∑_γ κ(γ · l) = 1` for every `l`,
   because the action is free. Hence `∑_l a(l) = ∑_l κ(l) ∑_γ a(γ · l)` for every family `a`.
   Equal orbit sums therefore give equal totals, so the first family also sums to `ν(C)`.

Conjugation invariance of `ν`, and stability of `Γ` under conjugation, are used only in step 3
for the second family. The proof never uses that `Γ` is all of `j⁻¹ Λ`; only `j(Γ) ⊆ Λ` (so
that `Γ` acts freely on `Λ`) and stability under conjugation. This lets the adelic application
take `Γ = U(F)` without proving `U(𝔸) ∩ P₀(F) = U(F)`. The strictness of `D` is used in step 2, at points `j w · g` that may form a `μ`-null set. Only countability of
`Λ` is needed for the sums; no topology is used.

## Scope

Only the displayed identity is proved. The theorem does not construct `C` or `D`, nor does it
identify `Γ` with the rational points of an adelic unipotent group or prove that conjugation by
`P₀(F)` preserves Haar measure on `U_P(𝔸)`. Those facts belong to the adelic instantiation.
