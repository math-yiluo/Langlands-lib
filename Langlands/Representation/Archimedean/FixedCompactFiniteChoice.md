# Compact-finite smooth fixed vectors on which a functional does not vanish

Module `Langlands.Representation.Archimedean.FixedCompactFiniteChoice`, namespace
`Langlands.Archimedean.FixedCompactFiniteChoice`.

## Statement

`exists_compactFinite_ne_zero`. Let `M` be a real Lie group modelled on a finite-dimensional real
normed space `A`, `E` a complex Hilbert space, `π : M →* (E →L[ℂ] E)` and `σ : Φ →* (E →L[ℂ] E)`
two commuting representations, and `L` a subgroup of `Φ`. Let `K` be a compact Hausdorff
topological group with a continuous homomorphism `r : K →ₜ* M` and a faithful finite-dimensional
representation `τ` on `ι → ℂ` with continuous orbits. Let `ξ : E →ₗ[ℂ] ℂ` satisfy
`‖ξ v‖ ≤ C · ∑_{Xs ∈ S} ‖dπ(Xs) v‖` for every smooth `v` in the `L`-fixed subspace
`SmoothInvariantSubspace.fixedSubspace σ L`. If `ξ v₀ ≠ 0` for a smooth `L`-fixed `v₀`, then there
is a smooth `L`-fixed `v` with `ξ v ≠ 0` that is `K`-finite:
`FiniteVectors.IsFiniteVector (CompactSmoothFiniteDensity.restrictedRepresentation π r) v`.

## Proof

Restrict `π` to the closed fixed subspace `U = fixedSubspace σ L`
(`SmoothInvariantSubspace.fixedRestriction`). With the probability Haar measure
`Analysis.compactProbabilityHaar K`, `CompactSmoothFiniteDensity.dense_finiteSmoothVectors` makes
the `K`-finite smooth vectors of the restriction dense in `DerivativeSmoothVectors`, the smooth
vectors with the topology of all derivative words. The functional `ξ` on the smooth vectors of the
restriction satisfies `IsContinuousOnSmoothVectors` (the derivatives of the restriction are those
of `π`, `iteratedLieDerivative_coe`), hence is continuous for that topology
(`continuous_of_isContinuousOnSmoothVectors`). The set where it does not vanish is open and contains
`v₀`, so it meets the dense set. The inclusion `U → E` intertwines the actions of `K`, so it
carries `K`-finite vectors to `K`-finite vectors (`IsFiniteVector.map`).

## Provenance

Internal: the approximation of a smooth vector by `K`-finite smooth vectors in the topology of the
derivative seminorms, through the Library's compact averaging and Stone–Weierstrass density of
finite weights.
