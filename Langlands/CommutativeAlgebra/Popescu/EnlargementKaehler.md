# Differentials of a simple purely transcendental field extension

`Enlargement.kaehler_basis_adjoin_transcendental`. Let `F'/F` be an extension of fields over `k`,
generated as a fraction field by an element `T` transcendental over `F`: every element of `F'` is
`f(T)/g(T)`. If the `dx_i` form a basis of `Ω_{F/k}`, then the `dx_i` together with `dT` form a
basis of `Ω_{F'/k}`. The family is indexed by `Fin t ⊕ Fin 1`.

Proof, using only the standard axioms.

1. Via `X ↦ T`, `F'` is the fraction field of `F[X]` (`IsFractionRing.of_field`). Hence `F'` is
   formally étale over `F[X]`, and formally smooth over `F` (`FormallySmooth.comp`).
2. `Ω_{F'/F} ≅ F' ⊗_{F[X]} Ω_{F[X]/F}` (`tensorKaehlerEquivOfFormallyEtale`) is free on `dT`,
   since `Ω_{F[X]/F}` is free on `dX` (`polynomialEquiv`).
3. The Jacobi–Zariski sequence `H₁(L_{F'/F}) → F' ⊗_F Ω_{F/k} → Ω_{F'/k} → Ω_{F'/F} → 0`
   (`H1Cotangent.exact_δ_mapBaseChange`, `exact_mapBaseChange_map`) has `H₁(L_{F'/F}) = 0` by
   formal smoothness. So `F' ⊗ Ω_{F/k} → Ω_{F'/k}` is injective, and its image is the kernel of
   `Ω_{F'/k} → Ω_{F'/F}`.
4. Linear independence and spanning are then checked directly.
   - A relation `Σ cᵢ dxᵢ + c dT = 0` maps to `c dT = 0` in `Ω_{F'/F}`, so `c = 0`, and then all
     `cᵢ = 0` by injectivity.
   - Any `ω` differs from a multiple of `dT` by an element of the image of `F' ⊗ Ω_{F/k}`.
