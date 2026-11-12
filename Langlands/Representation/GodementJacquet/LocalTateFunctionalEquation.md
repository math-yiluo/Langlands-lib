# The local functional equation for Laurent numerators

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It proves the scalar
local functional equation at the level of the Laurent numerators from
`LocalTateLaurent`. It first proves it for the indicators of `O` and of the
principal-unit levels `1 + ϖ^m O`, and then for the larger class of functions
the closure lemmas reach. The reduction of every Schwartz--Bruhat function to these cases is in
`LocalTateConductorProof`.

## The dual variable and the dual relation

`qUnit` is `q` as a complex unit. `dualUnit x = q⁻¹ x⁻¹` is an involution
(`dualUnit_dualUnit`). At `x = X_s = q^{-s}` it equals `X_{1-s}`
(`coe_dualUnit_spectralUnit`, from the published `spectralPoint_sub_one_sub`).

`DualRelation c a ℓ ℓ'` states that, for every complex unit `x`,

`ℓ'(q⁻¹ x⁻¹) = c · x^a · ℓ(x)`.

Here `ℓ` is the Laurent numerator for `χ`, `ℓ'` is the one for `χ⁻¹` and the
Fourier transform, and `ℓ(x)` denotes `laurentEval x ℓ`.

## Coset indicators as dilates

- `cosetIndicator_eq_dilate_of_mem`: if `x0 ∈ ϖ^n O`, then
  `1_{x0 + ϖ^n O} = 1_O(ϖ^{-n} ·)`.
- `cosetIndicator_eq_dilate_of_notMem`: if `x0 ∉ ϖ^n O`, then
  `1_{x0 + ϖ^n O} = 1_{1 + ϖ^m O}(x0⁻¹ ·)` with `m = n - ord x0 ≥ 1`.

## Base-case numerators

- `hasLaurentMellin_integer`: `1_O` has numerator the constant `[a = 0]`. Use
  the shell expansion with `A = M = 0`.
- `shellCoeff_unitLevel`: the order-zero shell coefficient of
  `1_{1 + ϖ^m O}` is `∫_{1 + ϖ^m O} η d^×u`, which is
  `[a ≤ m] μ^×(1 + ϖ^m O)`.
- `hasLaurentMellin_unitLevel`: for `m ≥ 1`, `1_{1 + ϖ^m O}` has numerator
  `P_η · [a ≤ m] μ^×(1 + ϖ^m O)`. Use the shell expansion with `A = 0`,
  `M = 1`.

## Gauss integrals on the dual side

The Fourier transform of `1_{1 + ϖ^m O}` is
`Ψ(y) = ψ(y) · ν(ϖ^m O) · 1_{ϖ^{-m} O}(y)` (from `LocalTateFourier`). Its
shell coefficients are `ν(ϖ^m O) · G_η(k)` for `k ≥ -m`
(`shellCoeff_of_fourier_unitLevel`), where `G_η` is the Gauss integral of
`LocalTateHaar`. By `gaussIntegral_eq_zero_of_ne`, at negative orders only
`k = -max(a, 1)` can contribute. So the finite sum in the dual shell expansion
has the single term at `k = -max(a,1)` when `max(a,1) ≤ m`, and is zero
otherwise (`sum_shellCoeff_fourier_unitLevel`).

## The functional-equation predicate

Fix `ψ`, the measure `ν`, the character `χ` and the natural number `a`.
`FEData c Φ` asserts the following:

- some Schwartz--Bruhat `Ψ` has values equal to the actual plus-sign Fourier
  integral `fourierIntegral ψ ν Φ`;
- there are Laurent numerators `ℓ` for `(χ, P_χ, Φ)` and `ℓ'` for
  `(χ⁻¹, P_{χ⁻¹}, Ψ)`, both with `HasLaurentMellin`;
- `DualRelation c a ℓ ℓ'` holds.

`feConstant` is

- `ν(O)` if `a = 0`;
- `ν(O^×-shell) · q^a · χ(ϖ)^a · G_{χ⁻¹}(-a)` if `a ≥ 1`,

where `ν(O^×-shell) = ν({v = 1})`.

Closure lemmas:

- `feData_zero`, `feData_add` and `feData_smul` hold for every `c`. The Fourier
  transform is linear (`HarmonicAnalysis.fourierTransform`), and numerators add.
- `feData_dilate`: if `Φ` satisfies `FEData c`, so does `Φ(b ·)`. Its
  transform is `abv(b)⁻¹ Ψ(b⁻¹ ·)` by `fourierIntegral_dilate`. Its numerators
  are `χ(b)⁻¹ T^{-ord b} ℓ` and `q^{ord b} χ(b)⁻¹ T^{ord b} ℓ'`, using
  `abv(b)⁻¹ = q^{ord b}`. The dual relation is preserved because
  `(q⁻¹x⁻¹)^{ord b} = q^{-ord b} x^{-ord b}`.

Base cases (assuming `HasIntegerConductor ψ` and `IsUnitConductor χ a`):

- `feData_integer`: `1_O` satisfies `FEData (feConstant)`. Its transform is
  `ν(O) 1_O`, and both numerators are the constant `[a = 0]` (times `ν(O)` on
  the dual side). The relation holds with `c = ν(O)` when `a = 0` and
  trivially when `a ≥ 1`.
- `feData_unitLevel`: for `m ≥ 1` and self-dual `ν`, `1_{1 + ϖ^m O}` satisfies
  `FEData (feConstant)`. The transform is the actual Fourier integral, realized
  as a Schwartz--Bruhat function by the published
  `exists_scalar_fourier_witness`. Its numerator comes from the shell
  expansion with `A = -m`, `M = 0`. Write `U = ν({v = 1})` and
  `B = ν(ϖ O)`, and use `μ^×(1 + ϖ^m O) = ν(ϖ^m O)/U` from `LocalTateHaar`.
  - If `a ≥ 1`: for `a ≤ m`, both sides equal
    `ν(ϖ^m O) G_{χ⁻¹}(-a) q^a x^a` up to the common unit factors. For
    `a > m`, both sides vanish.
  - If `a = 0`: `G_{χ⁻¹}(-1) = -B/U`. The identity reduces to
    `ν(O) = U + B` and `q B = ν(O)` (from `measure_ball`). The
    `linear_combination` step closes it.

## Provenance

This is the local functional equation of Tate's thesis (source
`tate-1967-thesis`, §2.4, Theorem 2.4.1) and of the 1979 survey
(`tate-1979-number-theoretic-background`, (3.2.1), (3.2.6)). Both are cited in
`LocalTateConductorStatement.md`. The implemented route is different from
Tate's: it verifies the Laurent-level identity directly on lattice-coset
indicators, and then extends it by linearity and dilation. It does not use
Tate's `Z(Φ, Ψ^) = Z(Φ^, Ψ)` argument. The predicates `DualRelation` and
`FEData` and the constant `feConstant` are internal devices of this proof.
