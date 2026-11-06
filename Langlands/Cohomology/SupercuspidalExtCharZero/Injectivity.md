# Injectivity of irreducible representations with compact coefficients

This module proves the injectivity half of the unchanged
`CompactCoefficientInjectiveProjectiveStatement`, given finite-dimensional fixed vectors.
The declaration is in `Langlands.Cohomology.SupercuspidalExtCharZero`.

## Statement

`injective_of_hasCompactCoefficients ρ hirr hc hadm` concludes `Injective ρ` in
`SmoothRep.{u, u, u} k G`. The hypotheses are:

- `k : Type u` is a field with `CharZero k`;
- `G : Type u` is a Hausdorff, locally compact, totally disconnected topological group;
- `ρ` is a smooth representation with `hirr : ρ.IsIrreducible` and
  `hc : HasCompactCoefficients ρ`;
- `hadm`: for every compact open subgroup `K`, the space
  `fixedVectors ρ.representation K` is finite-dimensional.

The final module discharges `hadm` with Worker 1643's
`finiteDimensional_fixedVectors`.

## Provenance

Vignéras (1996), Proposition I.7.10, printed page 62, proves injectivity over an
algebraically closed field. It uses projectivity of the contragredient and the identity
`V = (Ṽ)~` for admissible `V`. The implemented proof instead shows directly that `ρ` is
a retract of an injective object. It uses the retraction of
`Langlands.Cohomology.SupercuspidalExtCharZero.Retraction`. This route is derived for this
project.

## Implemented proof

1. `exists_coefficientMap_bijective` gives a compact open `U`, a `U`-fixed functional `ξ`
   and a `U`-fixed vector `w`. The coefficient map `Ψ` from `ρ` to itself is then
   bijective. It is promoted to an equivalence by
   `Representation.IntertwiningMap.ofBijective`.
2. The category has enough injectives (`Langlands.SmoothRep.enoughInjectives`, from
   `Langlands.Representation.Category.SmoothPartAdjunction`). So Mathlib's
   `Injective.ι ρ : ρ ⟶ Injective.under ρ` is a monomorphism into an injective object.
   Its underlying map is injective by `SmoothRep.mono_iff_injective`.
3. `exists_intertwining_comp_eq_coefficientMap` gives an intertwiner `r` from
   `Injective.under ρ` to `ρ` with `r ∘ ι = Ψ`.
4. The pair `ι` and `SmoothRep.ofHom (Ψ⁻¹ ∘ r)` is a `Retract ρ (Injective.under ρ)`. The
   identity `ι ≫ ofHom (Ψ⁻¹ ∘ r) = 𝟙 ρ` reduces to `Ψ⁻¹ (Ψ v) = v` through
   `SmoothRep.ofHom_hom`, `SmoothRep.hom_comp`, `SmoothRep.hom_ofHom` and
   `SmoothRep.hom_id`.
5. Mathlib's `Retract.injective` concludes that `ρ` is injective.
