# The coefficient of the cyclic orbit of the right `Φ⁻` sequence

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). It identifies the coefficient
of the published split-stage character comparison at the cyclic orbit with
`τ_(V_(r+2), θ_r) ⊗ ρ`, the `Φ⁻` quotient of `τ` tensored with `ρ`, computes its
action and proves its naturality and the scalar identity of the normalizations.
The cyclic piece is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle`.

## Provenance

All declarations are derived internal content. In BZ77 §7.2, printed p.471
(PDF p.32), source `bernstein-zelevinsky-1977-induced-i`, the open (cyclic)
orbit contributes `Φ⁻(τ) × ρ`; the coefficient computed here is its inducing
coefficient. The tensor-coinvariant identification is the character-localized
version of the published `rightPsiTensorEquiv`
(`MirabolicProductMinusRightPsiCoefficient`), proved here for an arbitrary
character of the radical; the real-power identity is the published
`rightPsi_scalar_identity_complex` at `m = k+1` and source rank `r+1`.

## Localized coinvariants of the inducing coefficient under `N`

For `τ` on `P_(r+1)` with carrier `W`, `ρ` on `GL_m` with carrier `V`, and any
character `θ : V_(r+1) → ℂˣ` of the radical:

- `rightPsiKernelCharacter θ` is `θ` on the published kernel subgroup
  `rightPsiKernel m r` through `rightPsiKernelEquiv` (its mirabolic block).
- `rightPsiLocalizedTensor_comp`: `([·] ⊗ id) ∘ χ_R(τ ⊠ ρ)(g) = θ(g) • ([·] ⊗ id)`
  for `g ∈ N`, since `g` acts by `τ(u) ⊗ 1` (published
  `rightPsiInducingCoefficient_kernel`).
- `rightPsiLocalizedTensorForward`, `rightPsiLocalizedTensorBilinear` and
  `rightPsiLocalizedTensorEquiv T τ ρ θ`: the `θ`-localized `N`-coinvariants of
  `rightPsiInducingCoefficient T τ ρ` are
  `Jacquet.Localization.Coinvariants τ (radical r) θ ⊗ V`, by the universal
  properties of both quotients; `_mk_tmul` sends `[w ⊗ v]` to `[w] ⊗ v` (`rfl`).
  For `θ = 1` this is the published `rightPsiTensorEquiv`.

## The kernel intersection

- `rightCycleKernelIntersection k r R` is the published `kernelIntersection` of
  `rightCycleRetraction` and `rightCycleInducing`, i.e. `A = HP ∩ ker rP`.
- `rightCycleIntersectionToKernel` and `rightCycleKernelToIntersection` pass
  between `A` and `S ∩ ker plusProjection` on underlying elements.

## The coefficient

For `T`, `ψ`, `k, r`, `τ` on `P_(r+2)` with carrier `W` and `ρ` on `GL_(k+1)` with
carrier `V`:

- `rightCycleCoefficient T k r τ ρ` is the published case (III) coefficient
  `rightPsiInducingCoefficient T τ ρ = χ_R (τ ⊠ ρ)` of shape `(k+1, r+1)` through
  `rightCycleInclusion`; `rightCycleStagesCoefficient` is its restriction to
  `HP = S ∩ P`.
- `rightCycle_relations_eq`: for a character `η` of `A` with
  `η a = θ_r(rightPsiKernelEquiv (rightCycleKernelEquiv a))`, where
  `θ_r = T.mirabolicTheta ψ r` (in the application `η` is the localized
  character and the hypothesis is `thetaPlus_rightCycle`), the localized
  relations of the restricted coefficient at `(A, η)` are the `θ_r`-localized
  relations of `rightPsiInducingCoefficient` at `rightPsiKernel (k+1) (r+1)`.
  Generators correspond through `rightCycleKernelEquiv`, which is bijective.
- `rightCycleCoefficientEquiv T ψ k r τ ρ η hη` is the resulting linear
  equivalence to `Jacquet.Localization.Coinvariants τ (radical (r+1)) θ_r ⊗ V`,
  whose first factor is the carrier of `Φ⁻τ`: `Submodule.quotEquivOfEq`
  followed by `rightPsiLocalizedTensorEquiv`; `_mk_tmul` sends `[w ⊗ v]` to
  `[w] ⊗ v` (`rfl`).
- `rightCycleCoefficientEquiv_section`: for `l ∈ K` with blocks
  `[[p, X], [0, a]]`, the class of the section action on `w ⊗ v` goes to
  `χ_R(…) • ([τ(successor p) w] ⊗ ρ(a) v)`, by
  `rightCoefficient_rightCycleSectionElement`.
- `rightCycleCoefficientEquiv_natural_tmul` and `_natural`: for morphisms
  `f₁ : τ ⟶ τ'`, `f₂ : ρ ⟶ ρ'` and a linear map acting by `f₁ ⊗ f₂` on pure
  tensors, the identification turns its class map into `Φ⁻(f₁) ⊗ f₂`
  (published `phiMinus_map_quotient`).

## The target action and the scalars

- `rightCycle_phiMinus_tmul`: on `[w] ⊗ b`, `Φ⁻τ(p) ⊗ ρ(a)` is
  `ν(p)^(-1/2) • ([τ(successor p) w] ⊗ ρ(a) b)` (published `phiMinus_action`).
- `determinantNorm_val_eq_projection`: `ν_(n+1)(g) = ν_n(projection g)` for
  `g ∈ P_(n+1)` (published `determinant_projection`).
- `rightCycle_scalar_eq`: with `ν = |det|` and `ν(p)` the norm of `p` as an
  element of `GL_(r+1)`,

  ```text
  φ⁻(l) · χ_H(l) · χ_R(successor l) = χ_R'(l) · φ⁻_r(p),
  ν(p)^(-1/2) ν(a)^(-1/2) · ν(a) · ν(p)^((k+1)/2) ν(a)^(-(r+2)/2)
    = ν(p)^((k+1)/2) ν(a)^(-(r+1)/2) · ν(p)^(-1/2),
  ```

  where `φ⁻` is `phiMinusCharacter T (k+r+1)` on `K`, `χ_H` the Haar character
  (`rightCycleHaarRatio_apply`, with `ν(l) = ν(p) ν(a)` by
  `determinantNorm_rightCycle`), `χ_R = T.rightCharacter (k+1) (r+1)` on the
  coefficient `(successor p, a)` of `plusSuccessor l`,
  `χ_R' = T.rightCharacter (k+1) r` on `rightCycleLevi l` and
  `φ⁻_r = phiMinusCharacter T r`. The two sides are the published
  `rightLeviCharacter` values, using `projection (successor p) = p` and
  `ν_r(projection p) = ν_(r+1)(p)`.

## Imports

The direct imports are `MirabolicProductMinusRightPhiCycleGroups` and
`MirabolicProductMinusRightPhiIdentityCoefficient` (for
`localization_tensor_ext_smul` and, through it, the published
`MirabolicProductMinusRightPsiCoefficient`). The complete import closure and the
restriction audit are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPhi.md`.
