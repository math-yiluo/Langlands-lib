# The coefficient of the identity orbit of the right `Φ⁻` sequence

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). It identifies the coefficient
of the published split-stage character comparison at the identity orbit with
`τ_(V_(r+2)) ⊗ ρ`, computes its action and proves its naturality and the scalar
identity of the normalizations. The identity piece is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity`.

## Provenance

All declarations are derived internal content. In BZ77 §7.2, printed p.471
(PDF p.32), source `bernstein-zelevinsky-1977-induced-i`, the identity orbit
contributes `Ψ⁻(τ) × (ρ|P_k)`; the coefficient computed here is its inducing
coefficient. The tensor-coinvariant identification reuses the published
`rightPsiTensorEquiv` (`MirabolicProductMinusRightPsiCoefficient`); the real
power identity is the published `rightPsi_scalar_identity_complex` at
`m = k+1` and source rank `r+1`.

## Localized coinvariants of a tensor product

`localization_tensor_ext_smul`: an identity `e ∘ f = c • (g ∘ e)` on
`Jacquet.Localization.Coinvariants ρ U θ` of a representation on `W ⊗ V` holds
if it holds on classes of pure tensors.

## The kernel intersection

- `rightIdentityKernelIntersection k r R` is the published `kernelIntersection`
  of `rightIdentityRetraction` and `rightIdentityInducing`, i.e. `A = HP ∩ ker rP`.
- `rightIdentityIntersectionToKernel` and `rightIdentityKernelToIntersection`
  pass between `A` and `S ∩ ker plusProjection` on underlying elements.

## The coefficient

For `T`, `k, r`, `τ` on `P_(r+2)` with carrier `W` and `ρ` on `GL_(k+1)` with
carrier `V`:

- `rightIdentityCoefficient T k r τ ρ` is the published case (III) coefficient
  `rightPsiInducingCoefficient T τ ρ = χ_R (τ ⊠ ρ)` through
  `rightIdentityInclusion`; `rightIdentityStagesCoefficient` is its restriction
  to `HP = S ∩ P`.
- `rightIdentity_relations_eq`: for any character `η` of `A` trivial on `A`
  (in the application, the localized character, trivial by
  `thetaPlus_rightStabilizer_one`), the localized relations of the restricted
  coefficient at `(A, η)` are the published kernel relations of
  `rightPsiInducingCoefficient` at `rightPsiKernel (k+1) (r+1)`. Generators
  correspond through `rightIdentityKernelEquiv`.
- `rightIdentityCoefficientEquiv T k r τ ρ η hη` is the resulting linear
  equivalence to `Jacquet.Localization.Coinvariants τ (radical (r+1)) 1 ⊗ V`:
  `Submodule.quotEquivOfEq` followed by `rightPsiTensorEquiv`;
  `_mk_tmul` sends `[w ⊗ v]` to `[w] ⊗ v` (`rfl`).
- `rightIdentityCoefficientEquiv_section`: for `l ∈ K` with blocks
  `[[A, B], [0, D]]`, the class of the section action on `w ⊗ v` goes to
  `χ_R(…) • ([τ(diag(A, 1)) w] ⊗ ρ(D) v)`, by
  `rightCoefficient_rightIdentitySectionElement`.
- `rightIdentityCoefficientEquiv_natural_tmul` and `_natural`: for morphisms
  `f₁ : τ ⟶ τ'`, `f₂ : ρ ⟶ ρ'` and a linear map acting by `f₁ ⊗ f₂` on pure
  tensors, the identification turns its class map into `Ψ⁻(f₁) ⊗ f₂`
  (published `psiMinus_map_quotient`).

## The target action and the scalars

- `rightIdentity_psiMinus_tmul`: on `[w] ⊗ b`, `Ψ⁻τ(A) ⊗ (ρ|P)(D)` is
  `ν(A)^(-1/2) • ([τ(diag(A, 1)) w] ⊗ ρ(D) b)` (published `psiMinus_action`).
- `rightIdentity_scalar_eq`: with `ν = |det|`,

  ```text
  φ⁻(l) · χ_H(l) · χ_R(diag) = χ_L(l) · ψ⁻(A),
  ν(A)^(-1/2) ν(D)^(-1/2) · ν(D) · ν(A)^((k+1)/2) ν(D)^(-(r+2)/2)
    = ν(A)^((k+1)/2) ν(D)^(-(r+1)/2) · ν(A)^(-1/2),
  ```

  where `φ⁻` is `phiMinusCharacter T (k+r+1)` on `K`, `χ_H` the Haar character
  (`rightIdentityHaarRatio_apply`), `χ_R = T.rightCharacter (k+1) (r+1)`,
  `χ_L = T.leftCharacter (r+1) k` and `ψ⁻ = psiMinusCharacter T (r+1)`.

## Imports

The direct imports are `MirabolicProductMinusRightPhiIdentityGroups` and the
published `MirabolicProductMinusRightPsiCoefficient`. The complete import
closure and the restriction audit are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPhiIdentity.md`.
