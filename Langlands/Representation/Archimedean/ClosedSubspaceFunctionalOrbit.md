# Orbits of functionals bounded on the smooth vectors of a closed invariant subspace

Module `Langlands.Representation.Archimedean.ClosedSubspaceFunctionalOrbit`, namespace
`Langlands.Archimedean.ClosedSubspaceFunctionalOrbit`.

## Statement

`contMDiff_and_mfderiv`. Let `M` be a real Lie group modelled on `A`, `E` a complex Hilbert space
and `π : M →* (E →L[ℂ] E)` with `⟪π g u, π g v⟫ = ⟪u, v⟫`. Let `F₀` be a closed subspace of `E`
with `π g F₀ ⊆ F₀`, and `ℓ : E →ₗ[ℂ] ℂ` a linear form with
`‖ℓ v‖ ≤ C · ∑_{Xs ∈ S} ‖dπ(Xs) v‖` for every smooth vector `v ∈ F₀`, for a finite set `S` of
words and a constant `C`. For every smooth `w ∈ F₀`:

- `g ↦ ℓ (π g w)` is `C^∞` (`ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞`);
- for `g ∈ M` and `X ∈ A`, the derivative at `1` of `h ↦ ℓ (π (g h) w)` in the direction `X`
  is `ℓ (π g (dπ(X) w))`.

No density of smooth vectors in `E` or in `F₀` and no continuity of `ℓ` on `E` is assumed.

## Proof

Let `W₀ = smoothVectors 𝓘(ℝ, A) π ⊓ F₀`, which is `π`-invariant (`isSmoothVector_apply`), and
`U` its closure: a closed, hence complete, `π`-invariant subspace contained in `F₀`. Let `π'` be
the restriction of `π` to `U` (`SmoothInvariantSubspace.restriction`), which is unitary. The
smooth vectors of `π'` are the smooth vectors of `π` lying in `U` (`isSmoothVector_coe`,
`isSmoothVector_of_coe`), so they contain `W₀` and are dense in `U`. On them, `ℓ` composed with
the inclusion satisfies `IsContinuousOnSmoothVectors` with the same `S` and `C`, because the
derivatives of `π'` are those of `π` (`iteratedLieDerivative_coe`). The Library theorem
`smoothFunctionalOrbit` (`SmoothFunctionalOrbitStatement`) applied to `π'` and the vector `w` gives
the smoothness and the derivative, and `lieDerivative_coe` identifies `dπ'(X) w` with `dπ(X) w`.

## Provenance

Internal. It reduces the case of a functional that is continuous only on the smooth vectors of a
closed invariant subspace (for instance those fixed by an open subgroup of a commuting group) to
the published `SmoothFunctionalOrbitStatement`.
