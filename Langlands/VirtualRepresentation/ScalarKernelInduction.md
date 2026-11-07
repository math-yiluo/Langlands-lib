# Scalar lifts of induced characters of the normalized image

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`.
It continues `Langlands.VirtualRepresentation.ScalarKernelGroup`, in the same
namespace `Langlands.VirtualRepresentation.ScalarKernel`. It computes the scalar
lift of a representation of the normalized image induced from a
one-dimensional character, and proves the continuity statements needed later.

Throughout, `ρ : Representation ℂ S V`, `A` is a subgroup of
`normalizedImage ρ` and `ψ : A →* ℂˣ`.

## Products and inverses

`rho_mul_of_eq`, `rho_inv_of_eq` and `rho_mul_inv_of_eq` multiply, invert and
divide decompositions `ρ s = c • endOf ρ h`. The inverse uses uniqueness of
inverses in `End V`. `scalar_ne_zero_of_endOf`: if `endOf ρ h = c • 1`, then
`c ≠ 0`, since `h` is a unit (for nontrivial `V`). `endOf_one` is the identity
`endOf ρ 1 = 1`.

## The subgroup `T` and the character `θ`

- `scalarPreimage ρ A` is the subgroup of `s : S` with `ρ s = z • endOf ρ a`
  for some `a ∈ A` and `z : ℂˣ`. `mem_scalarPreimage` is its introduction
  rule. `le_scalarPreimage`: every subgroup `N` on which `ρ` is scalar is
  contained in it, using `a = 1`.
- `IsTautOn ρ A ψ`: `ψ a = c` for every `a ∈ A` with `endOf ρ a = c • 1`. That
  is, `ψ` agrees on the scalar elements of `A` with their scalar.
- `theta_eq_aux`: under `IsTautOn`, `z • a = z' • a'` (with `a, a' ∈ A`)
  implies `z ψ(a) = z' ψ(a')`. The element `a a'⁻¹` is the scalar `z'/z`, so
  `ψ(a a'⁻¹) = z'/z`.
- `scalarCharacter ρ hψ : scalarPreimage ρ A →* ℂˣ` sends `t` to `z ψ(a)` for
  a chosen decomposition `ρ t = z • a`. `scalarCharacter_spec`: the value is
  the same for every decomposition. Multiplicativity follows from
  `rho_mul_of_eq`.

## The induced equivalence

Let `χ : Representation ℂ A ℂ` with `χ a x = ψ a * x` (hypothesis `hχ`). The
induced representation `Ind_A ψ` is Mathlib's
`Representation.coind A.subtype χ`, on functions `f` on the normalized image
with `f (a x) = ψ(a) f(x)`.

- `coindV_apply_mul` records this equivariance. `taut_coind_eval` is the value
  at the identity of `tautPart_key`: on the tautological part,
  `c₁ • h₁ = c₂ • h₂` implies `c₁ f(h₁) = c₂ f(h₂)`.
- `tautPart_coind_eq_bot`: if `IsTautOn ρ A ψ` fails, the tautological part of
  `Ind_A ψ` is zero. Choose `a ∈ A` with `endOf ρ a = c • 1` and `ψ a ≠ c`. For
  `f` in the tautological part, `f(x a) = c f(x)`. Also `a` is central, so
  `f(x a) = f(a x) = ψ(a) f(x)`. Hence `f(x) = 0`.
- `coindCharacter ρ hψ` is `Ind_T θ`, Mathlib's coinduced representation from
  `T = scalarPreimage ρ A` of the published character line
  `characterLine (scalarCharacter ρ hψ)`. `coindCharacter_eval`: for `F` in it,
  `ρ (s₁ s₂⁻¹) = w • a` with `a ∈ A` implies `F(s₁) = w ψ(a) F(s₂)`.
- `toCoindCharacter` sends `f` in the tautological part to
  `F(s) = z_s f(h_s)`, where `ρ s = z_s • h_s` is the chosen lift.
  `toCoindFun` sends `F` to `f(h) = c_h⁻¹ F(s_h)`, where
  `ρ s_h = c_h • h` is the chosen preimage. Membership in the coinduced spaces,
  the tautological condition and the two inverse identities all follow from
  `taut_coind_eval` and `coindCharacter_eval`.
- `coindScalarLiftEquiv ρ χ hχ hψ`: in the tautological case, the scalar lift
  of `Ind_A ψ` is equivalent to `Ind_T θ` as representations of `S`. The
  equivariance is again `taut_coind_eval`, applied to
  `ρ (s s') = (z_s z_{s'}) • (h_s h_{s'})`.

## Continuity

Let `S` be a topological group and `ρ` continuous, in the published sense
`(FiniteRepresentation.of ρ).IsContinuous`. Let `N` be an open subgroup on
which `ρ` is scalar.

- `scalarTrace` is `(finrank V)⁻¹ · trace`, a linear functional with
  `scalarTrace (c • 1) = c` (`scalarTrace_smul_one`).
  `continuous_scalarTrace_comp`: `s ↦ scalarTrace (ρ s)` is continuous,
  because linear maps out of the module topology are continuous.
- `isContinuous_scalarLift`: every scalar lift (with finite-dimensional `Y`) is
  continuous. On `N` it equals `s ↦ scalarTrace (ρ s) • 1`, by
  `scalarLift_of_eq` with the decomposition `ρ n = c • 1`. This function is
  continuous, so the lift is continuous at `1`. Mathlib's
  `continuous_of_continuousAt_one` applies, because the endomorphism ring with
  its module topology is a topological ring.
- `continuous_scalarCharacter` and `continuousScalarCharacter`: `θ` is
  continuous. On the open subgroup `N.subgroupOf T` of `T` its complex values are
  `scalarTrace (ρ t)`. So the homomorphism to `ℂ` is continuous at `1`, hence
  continuous. Continuity into `ℂˣ` then follows from `Units.continuous_iff`,
  since `θ(t)⁻¹ = θ(t⁻¹)`.

## Dependencies

The module imports `Langlands.VirtualRepresentation.ScalarKernelGroup`,
`Langlands.Weil.Representation.CharacterLine` (`characterLine`) and Mathlib's coinduced representations and module
topology.
