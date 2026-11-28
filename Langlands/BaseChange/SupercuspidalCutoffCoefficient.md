# Cut-off coefficients of supercuspidal representations of `GL_n`

The module `Langlands.BaseChange.SupercuspidalCutoffCoefficient` (namespace
`Langlands.BaseChange.SupercuspidalCutoff`) constructs, for a supercuspidal representation `π`
of `GL_n(F)`, the cut-off matrix coefficients `g ↦ 1[0 ≤ ord_F det g < n] · ℓ(π(g⁻¹) x)` as
Schwartz–Bruhat functions and proves that they have vanishing constant terms.

Throughout, `F` is a field with `[ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]` (any characteristic), `GL_n(F)` is `GeneralLinear n F` with its
topology, and `(⟨⟩ : LocalFieldData F)` is the Library's bundle of these instances (module
`Langlands.LocalField.LocalFieldData`).

## The level function

- `detOrd g = ord_F (det g)`, the normalized valuation (`LocalFieldData.ord`) of the
  determinant. `detOrd_mul`, `detOrd_one`, `detOrd_inv`: it is additive.
- `mem_ker_determinantNorm_iff`: `g` lies in the kernel of the normalized determinant norm
  `|det|` (`LocalFieldData.determinantNorm`) if and only if `detOrd g = 0`, because
  `|x| = q^{-ord x}` with `q > 1`.
- `isLocallyConstant_detOrd`: `detOrd` is locally constant, since it is constant on the cosets
  of the open subgroup `ker |det|` (`LocalFieldData.isOpen_ker_determinantNorm`).
  `isLocallyConstant_indicator_detOrd`: the indicator of a set `{g | p (detOrd g)}` times a
  locally constant function is locally constant.
- `uniformizerUnit` is the Library's uniformizer of `F` as a unit, `centralUniformizer` its
  scalar matrix; `centralUniformizer_mem_center` and `detOrd_centralUniformizer`
  (`detOrd = n`).

## Coefficients and their cut-off

For a representation `π` of `GL_n(F)` on `V` and a linear form `ℓ`:

- `coeff π ℓ x g = ℓ(π(g⁻¹) x)`; `coeff_rho`: `coeff π ℓ (π h x) g = coeff π ℓ x (h⁻¹ g)`;
  `coeff_add`, `coeff_smul`; `isLocallyConstant_coeff` for smooth `π`.
- `hasCompactSupport_levelSet_coeff`: if `0 < n`, `π` is supercuspidal
  (`GeneralLinear.IsSupercuspidal`, module `Langlands.Representation.Classification.Supercuspidal`)
  and `ℓ` is smooth for the contragredient action (`IsSmoothVector π.dual ℓ`), then on each level
  set `{detOrd = j}` the coefficient has compact support. If the level set contains `t`, it
  equals `t · ker |det|` and `ℓ(π(g⁻¹) x) = ℓ(π((t⁻¹ g)⁻¹) π(t⁻¹) x)`; the coefficient
  `g₀ ↦ ℓ(π(g₀) π(t⁻¹) x)` has compact support on `ker |det|` by the Library's
  `AllField.GodementJacquet.hasCompactSupport_determinantUnit_coefficient` (module
  `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCoefficientTests`), and so has
  its composition with inversion.
- `cutoffFun π ℓ x` is the indicator of the window `{0 ≤ detOrd g < n}` (`PeriodicWindow.window`,
  module `Langlands.BaseChange.PeriodicWindowIntegral`) times `coeff π ℓ x`. It is locally
  constant (`isLocallyConstant_cutoffFun`) and, as the sum of its `n` level-set pieces, compactly
  supported (`hasCompactSupport_cutoffFun`). It is linear in `x` (`cutoffFun_add`,
  `cutoffFun_smul`), and `cutoffFun_rho_of_detOrd_eq_zero`: for `detOrd k = 0`,
  `cutoffFun π ℓ (π k x) g = cutoffFun π ℓ x (k⁻¹ g)`.
- `cutoff π ℓ hn hπ hℓ : V →ₗ[ℂ] SchwartzBruhat (GeneralLinear n F)` bundles these functions
  (`cutoff_apply`).

## Vanishing constant terms

`hasVanishingConstantTerms_cutoff`: every `cutoff π ℓ hn hπ hℓ x` satisfies the Library's
`HasVanishingConstantTerms` (module `Langlands.BaseChange.CuspForm`). Let `B` be a block shape
with at least two blocks, `U` its unipotent radical with a Haar measure, and `a`, `b ∈ GL_n(F)`.

1. Integrability: `u ↦ cutoff(s)(a u b)` is continuous with compact support on the closed
   subgroup `U`, hence integrable.
2. The linear form `L(s) = ∫_U cutoff(s)(a u b) du` is invariant under `π(k)` for every `k` in
   the conjugate `a U a⁻¹` (`BlockShape.conjugateUnipotent`): writing `k = a u₀ a⁻¹`, one has
   `detOrd k = 0` (unipotent elements have determinant `1`,
   `BlockShape.determinant_eq_one_of_mem_unipotentSubgroup`), so
   `cutoff(π(k) s)(a u b) = cutoff(s)(a u₀⁻¹ u b)`, and left invariance of the Haar measure on `U`
   removes `u₀⁻¹`.
3. Hence `L` factors through the Jacquet coinvariants of `π` along `a U a⁻¹`
   (`Jacquet.lift_mk`), which vanish because `π` is supercuspidal and the parabolic subgroup of
   `B` is proper (`CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top`). So
   `L(x) = 0`.

The proof follows the Library's `TraceFormula.globalizationLocalCoefficient_vanishing` (module
`Langlands.TraceFormula.GlobalizationLocalCoefficient`), with the window `{0 ≤ detOrd < n}` in
place of the determinant-unit subgroup.

## Provenance

The cut-off by the open and closed set `{0 ≤ v_F(det g) < n}` is the one described in the
Markdown of the Library's statement `SupercuspidalEllipticPseudoCoefficientStatement` (step 2 of
its sketch). The vanishing of the constant terms of a cut-off supercuspidal coefficient is
proved here directly from the Library's definition of supercuspidality (vanishing Jacquet
coinvariants). Constant terms enter the descent of orbital integrals in Kazhdan, *Cuspidal
geometry of p-adic groups* (1986), source ID `kazhdan-1986-cuspidal-geometry`, §5, proof of
Lemma 7 (printed p. 26), where the functions whose orbital integrals vanish off the elliptic set
are described through their constant terms `f^P`.
