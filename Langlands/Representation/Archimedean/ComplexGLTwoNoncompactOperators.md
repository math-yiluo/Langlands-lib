# Operators on the `GL_2(ℂ)` principal series in the noncompact picture

Module `Langlands.Representation.Archimedean.ComplexGLTwoNoncompactOperators`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`).

## Setting

* `Xd d` is the space `ComplexSwapJacquet.KFs 2 (List.ofFn d)` of `U(2)`-finite functions in the
  standard module (the `kFiniteFunctions` of the statement), and `πd d` is the Library action
  `complexStandardLie 2 (List.ofFn d)` of `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ)` on it.
* `ncpL d : Xd d →ₗ[ℂ] (ℂ → ℂ)` is the noncompact picture `v ↦ (z ↦ v(w n(z)))` as a linear map
  (`ncpL_apply`, `ncpL_eq`).
* `ncpL_tmul`: `π(c ⊗ X)` is `c` times `π(1 ⊗ X)`. `ncpL_single01`, `ncpL_single10` and
  `ncpL_single00` restate the formulas of `ComplexGLTwoNoncompactPicture` for `π(1 ⊗ c E_ab)`,
  using that `π(1 ⊗ X)` is the right derivative `R(X)` (Library `ComplexSwapJacquet.coe_lie`).

## The elements used

* `eD = D = (1 ⊗ E_01 - i ⊗ i E_01)/2`, `eDb = D̄ = (1 ⊗ E_01 + i ⊗ i E_01)/2`;
* `eF = F = (1 ⊗ E_10 - i ⊗ i E_10)/2`, `eFb = F̄ = (1 ⊗ E_10 + i ⊗ i E_10)/2`;
* `eH = H = 1 ⊗ i E_00`, `eXp = X₊ = D - F̄`, `eXm = X₋ = F - D̄`, `eP = P = D + F̄`.

With `φ = φ_v`, `p = pp d`, `q = qq d`, and `∂`, `∂̄` the Wirtinger derivatives, the
noncompact picture of `π(Y) v` is (`ncpL_eD`, `ncpL_eDb`, `ncpL_eF`, `ncpL_eFb`, `ncpL_eH`,
`ncpL_eXp`, `ncpL_eXm`, `ncpL_eP`):

| `Y` | `φ_{π(Y) v}` |
| --- | --- |
| `D` | `∂φ` |
| `D̄` | `∂̄φ` |
| `F` | `-(z² ∂φ + (p + 1) z φ)` |
| `F̄` | `-(z̄² ∂̄φ + (q + 1) z̄ φ)` |
| `H` | `i l_1 φ - i z ∂φ + i z̄ ∂̄φ` |
| `X₊` | `∂φ + z̄² ∂̄φ + (q + 1) z̄ φ` |
| `X₋` | `-(z² ∂φ + (p + 1) z φ) - ∂̄φ` |
| `P` | `∂φ - (z̄² ∂̄φ + (q + 1) z̄ φ)` |

Each is a linear combination of the `c = 1` and `c = i` cases of the basic formulas
(`kappa_one_I`: `κ_1(i) = i l_1`), closed by `linear_combination` with `i² = -1`.

## The compact directions

* `Y0 = i E_00`, `Y1 = E_01 - E_10`, `Y2 = i E_01 + i E_10` are skew-Hermitian
  (`star_Y0`, `star_Y1`, `star_Y2`), so they lie in the Lie algebra of `U(2)`.
* `eH_eq`: `H = 1 ⊗ Y0`; `eXp_eq`: `X₊ = (1/2) ⊗ Y1 - (i/2) ⊗ Y2`.
* `compact_stable`: a `U(2)`-stable subspace `W` of `X(d)` is stable under `H` and `X₊`. The
  Library's `ComplexJacquetFinite.skew_stable` gives stability under `π(1 ⊗ Y)` for
  skew-Hermitian `Y` (for the `(𝔤, K)`-module `X(d)`, `isComplexGKModule_complexStandardModule`).
* `lie_Y0_Y1`: `[Y0, Y1] = Y2`, `lie_Y0_Y2`: `[Y0, Y2] = -Y1` (matrix computations), and
  `eH_eXp`: `H X₊ v = X₊ H v + i X₊ v`, i.e. `[H, X₊] = i X₊`, from these and the Library's
  `ComplexSwapJacquet.lie_comm` (the action of `1 ⊗ X` respects commutators).

## Injectivity

* `principalSeriesCharacter_ne_zero`: the modulus-twisted character `δχ` never vanishes.
* `apply_lowerChart`: for `z ≠ 0`, `f(1 + z E_10) = φ_f(1/z) / δχ(t)`, where `t` is the Library's
  `chartTorus 0 1 (1/z)`; this is the Library's `ComplexSwapJacquet.apply_chart_eq` at `1/z`.
* `eq_zero_of_ncp_eq_zero`: if `φ_f = 0` then `f = 0`. By `apply_lowerChart`, `f` vanishes on
  `1 + z E_10` for `z ≠ 0`, hence at `1` by continuity of `z ↦ f(1 + z E_10)` (Library
  `contDiff_apply_lowerChart`, `lowerChart_zero`). For `g` with `g_10 = 0`,
  `g = diag(g_00, g_11) · n(g_01/g_00)`, so `f(g) = δχ(·) f(1) = 0`. For `g_10 ≠ 0`,
  `g = diag(a, g_10) · n(g_00/a) · w n(g_11/g_10)` with `a = g_01 - g_00 g_11/g_10 ≠ 0`, so
  `f(g)` is a multiple of `φ_f(g_11/g_10) = 0`. Both factorizations are checked entrywise, and
  the transformation law of the standard module (`hf.2`) moves the upper triangular factor out.
* `ncpL_injective`: `ncpL d` is injective.

## The Weyl element

* `wU` is `w = [[0, 1], [1, 0]]` as an element of `U(2)`, and `toUnits_wU` identifies it with
  `complexGLTwoWeyl`.
* `wn_mul_weyl`: `w n(z) w = 1 + z E_10` (the Library's `lowerChart 0 1 z`).
* `ncpL_rho_wU`: `φ_{ρ(w) v}(z) = v(1 + z E_10)`, where `ρ` is the right-translation action
  `complexStandardRep` of `U(2)`.
