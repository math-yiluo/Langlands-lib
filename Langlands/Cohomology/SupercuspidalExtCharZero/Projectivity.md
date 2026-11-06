# Projectivity of irreducible representations with compact coefficients

This module proves the projectivity half of the unchanged
`CompactCoefficientInjectiveProjectiveStatement`. The declaration is in
`Langlands.Cohomology.SupercuspidalExtCharZero`.

## Statement

`projective_of_hasCompactCoefficients ρ hirr hc` concludes `Projective ρ` in
`SmoothRep.{u, u, u} k G`. The hypotheses are:

- `k : Type u` is a field with `CharZero k`;
- `G : Type u` is a Hausdorff, locally compact, totally disconnected topological group;
- `ρ` is a smooth representation of `G` over `k`, with `hirr : ρ.IsIrreducible` and
  `hc : HasCompactCoefficients ρ`, the Library predicate of
  `Langlands.Cohomology.SupercuspidalExtCharZero.Statement`.

No Haar measure, σ-compactness or unimodularity is assumed.

## Provenance

The lifting is the one in Vignéras (1996), proof of Theorem I.7.9 a), printed page 61.
Given a surjection `p : W₁ → W₂` and `j : V → W₂`, Vignéras chooses `v₀`, `ṽ₀` with
`⟨ṽ₀, v₀⟩ = 1` and `w₁` with `p(w₁) = j(v₀)`. The coefficient of `(v₀, ṽ₀)`, acting on
`w₁`, lifts `j`, because the formal degree normalizes the corresponding self-map of `V`
to the identity. That theorem is over an algebraically closed field. Here no formal
degree is used. The bijective coefficient map of
`Langlands.Cohomology.SupercuspidalExtCharZero.CoefficientMap`, a counting-sum version of
that self-map, is inverted instead. This adaptation is derived for this project.

## Implemented proof

1. `exists_coefficientMap_bijective` gives a compact open subgroup `U`, a `U`-fixed
   functional `ξ` and a `U`-fixed vector `w` such that the intertwiner
   `Ψ = coefficientIntertwiningMap` from `ρ` to itself is bijective. It is promoted to an
   equivalence of representations by `Representation.IntertwiningMap.ofBijective`.
2. Let `f : ρ ⟶ X` and an epimorphism `e : E ⟶ X` be given. By
   `SmoothRep.epi_iff_surjective`, `e` is surjective. Choose `y₀` with `e y₀ = f w`.
3. Put `y = averageMap E U y₀`, which is fixed by `U`. Averaging commutes with `e`
   (`averageMap_commute`), and `f w` is `U`-fixed, so averaging leaves it unchanged
   (`averageMap_id`). Hence `e y = f w`.
4. The lift is `SmoothRep.ofHom` of the coefficient intertwiner from `ρ` to `E` at
   `(U, ξ, y)`, composed with `Ψ⁻¹`. For a vector `v`, naturality
   (`map_coefficientMap_intertwining`) gives
   `e (coefficientMap ρ E U ξ y (Ψ⁻¹ v)) = coefficientMap ρ X U ξ (e y) (Ψ⁻¹ v)`. With
   `e y = f w` and naturality for `f` this is `f (Ψ (Ψ⁻¹ v)) = f v`.
5. The equality of morphisms `lift ≫ e = f` is reduced to this equality of underlying
   maps by `SmoothRep.ofHom_hom`, `SmoothRep.hom_comp` and `SmoothRep.hom_ofHom`.

The averaging operations `averageMap`, `averageMap_mem_fixedVectors`,
`averageMap_commute` and `averageMap_id` are Worker 1643's, from
`Langlands.Representation.Compact.CharZeroAverage`. `SmoothRep.epi_iff_surjective` is
from `Langlands.Representation.Category.Abelian`.
