# Twisting Hopf points by automorphisms of the character group

Author: Worker 1421.

Endomorphisms `γ` of an additive group `M` act on Hopf points
`A → C ⊗[R] R[M]` by `mapDomain γ` on the group-algebra factor. Geometrically,
a homomorphism `D(M) → Spec A` is precomposed with the endomorphism `D(γ)` of
`D(M)`. This module defines the twist and transports it to Worker 950's
representing algebra `FiniteBialgebraHom.HomAlgebra R A R[M]`. The result is
the action of `Aut(M)` used in the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. It is an internal module.

## Points

- `twistPoint γ f := (id ⊗ mapDomain γ) ∘ f`.
- `scalarMap_comp_map_mapDomain` and `toGroupAlgebra_twistPoint`: under
  `C ⊗ R[M] ≅ C[M]`, the twist is `mapDomain γ`.
- `isHopfPoint_twistPoint`: twists of Hopf points are Hopf points, by
  `HopfPointBridge.isHopfPoint_iff` and `IsHopfPoint.mapDomain`.
- `pushPoint_twistPoint`: twisting commutes with change of coefficients.
- `twistPoint_twistPoint`, `twistPoint_id`: functoriality in `γ`.

## Action on the representing algebra

Assume `R[M]` is finite free over `R` and `A` is finitely presented, so that
Worker 950's `HomAlgebra` and `homEquiv` are available. `W` denotes
`HomAlgebra R A R[M]`.

- `twistHom γ : W →ₐ[R] W` corresponds under `homEquiv` to the twist of the
  universal Hopf point (`homEquiv_twistHom`, `pushPoint_twistHom`).
- `homEquiv_comp_twistHom`: precomposing a point `g : W → C` with
  `twistHom γ` twists the corresponding Hopf point by `γ`.
- `twistHom_comp`: `twistHom γ ∘ twistHom δ = twistHom (δ ∘ γ)`; and
  `twistHom_id`. Both follow from injectivity of `homEquiv`.
- `twistEquiv γ`: for an automorphism `γ` of `M`, the algebra automorphism
  with inverse `twistHom γ⁻¹` (`twistEquiv_apply`).
- `twistAction : Multiplicative (AddAut M) →* (W ≃ₐ[R] W)`: `γ` acts by
  `twistEquiv γ⁻¹` (Mathlib's `AddAut M` is an additive group, hence
  `Multiplicative`). It is a group homomorphism by `twistHom_comp` and
  `twistHom_id`.
