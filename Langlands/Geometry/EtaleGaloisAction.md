# Galois actions on étale cohomology of a base change

Author: Worker 13. Built on `Langlands.Geometry.EtaleConstantCohomology` (this
submission) and Mathlib's schemes, spectra and pullbacks.

Let `K` and `L` be commutative rings in universe `u` with `Algebra K L`, let
`X : Scheme.{u}`, and let `f : X ⟶ Spec K`.

## Definitions

- `baseChange K L f` is the pullback `X ×_{Spec K} Spec L` of `f` and
  Mathlib's `Spec.algebraMap K L`.
- `specMap σ` is the morphism `Spec L ⟶ Spec L` of a `K`-algebra automorphism
  `σ : L ≃ₐ[K] L`.
  - `specMap_comp_algebraMap`: it lies over `Spec K`.
  - `specMap_comp`: `specMap σ ≫ specMap τ = specMap (σ * τ)`. Spectra
    compose contravariantly, and multiplication in `L ≃ₐ[K] L` is
    composition.
  - `specMap_one`: `specMap 1 = 𝟙`.
- `baseChangeMap f σ` is Mathlib's `pullback.map` of `𝟙 X`, `specMap σ` and
  `𝟙 (Spec K)`. `baseChangeMap_comp` and `baseChangeMap_one` follow from
  `pullback.map_comp` and `pullback.map_id`.
- `baseChangeAut f σ` is the automorphism with inverse `baseChangeMap f σ⁻¹`.
- `galoisAut f : (L ≃ₐ[K] L) →* (Aut (baseChange K L f))ᵐᵒᵖ` sends `σ` to
  `baseChangeAut f σ` in the opposite automorphism group. This matches the
  convention of `EtaleCohomologyAction`.
- `galoisCohomologyRep f R M n : Rep R (L ≃ₐ[K] L)` is
  `EtaleCohomologyAction.constantCohomologyRep` for `galoisAut f`. It is the
  degree `n` étale cohomology of `X ×_{Spec K} Spec L` with constant
  coefficients `M`, with the action of `L ≃ₐ[K] L` through the second
  factor. Its underlying module is the published
  `EtaleDerivedSections.constantCohomology` of the base change at `M`, by
  `EtaleCohomologyAction.constantCohomologyIso`.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), Theorem 5.7, printed p.313, considers the
representation of `Gal(F̄/F)` on `H^{n-1}(S_K(N), W)[π]` and the action of
decomposition groups. Worker 13 read this passage in the original. For a field
`K` and a separable closure `L`, `L ≃ₐ[K] L` is the absolute Galois group.
Then `galoisCohomologyRep` is the Galois representation on étale cohomology
of `X_L` with constant coefficients. Not treated here:
- the Shimura varieties themselves;
- coefficient systems other than constant ones;
- continuity for the Krull topology;
- compact supports and Hecke operators;
- any comparison with other conventions for the action, such as the inverse
  action.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Project imports outside this submission are present in Library commit
`0686b4fa6c8df22845bba2e2668a723a41d47c84`.
