# Geometric reductivity excludes coordinates shifted by a nonconstant function

Author: Worker 1502. Internal helper for the proof of
`AffineHomogeneousQuotientReductiveStatement`. The argument is derived here and does not follow a
cited source. The input it uses is the published statement
`ReductiveGeometricReductivityStatement` (Haboush's theorem; MFK, *Geometric Invariant Theory*,
3rd ed., Appendix 1.A, Theorem A.1.0, registered as `mumford-fogarty-kirwan-1994-git-3rd`), and it
is used only as a hypothesis.

## Definitions and transfer

- `IsGeometricallyReductive G`, for a group scheme `G` over a field `k`, is the conclusion of
  `ReductiveGeometricReductivityStatement` for this one `G`. For every coordinate representation
  `ρ` and nonzero fixed vector `v` there is a homogeneous `F` of positive degree with
  `F(ρ(g) x) = F(x)` for all points `g` over all test schemes and all `x`, and with `F(v) ≠ 0`.
  This is definition (iii) of MFK, Appendix to Chapter 1, Section A, printed p.191 (PDF page
  index 202, 0-based): “geometrically reductive if, whenever G → GL(V) is a rational
  representation and 0 ≠ v ∈ V^G, then for some r > 0, there is an F ∈ (Symm^r V*)^G with
  F(v) ≠ 0.” Here `V = kⁿ` with a finite coordinate type `n : Type`, `Symm^r V*` is the space of
  homogeneous polynomials of degree `r` in `MvPolynomial n k`, and invariance of `F` is required
  on points over every test scheme, as in the Library's statement.
- `isGeometricallyReductive_of_statement`: the statement gives `IsGeometricallyReductive G` for
  every pseudo-reductive `G` over an algebraically closed field.
- `IsGeometricallyReductive.of_iso`: the property transfers along an isomorphism `G' ≅ G`, by
  restricting representations along the inverse.

## Evaluation on the corepresented model

For a corepresented group `Corepresented.groupScheme F e` with representing algebra `B`,
`evalAt e x : B →ₐ Γ(T, 𝒪_T)` is the classifying algebra map of a point `x` over `T`.
`evalAt_apply` identifies it with pulling back `(ΓSpecIso B).inv b` along `x`. `algebraMap_algΓ`
records that the algebra structure on `Γ(T, 𝒪_T)` is `scalarMap T`.

## Main theorem `false_of_isShift`

Let `K` be algebraically closed and `G' = Corepresented.groupScheme F e` with
`IsGeometricallyReductive G'`. Put the Library bialgebra structure `AffineLinearEmbedding.bialgebra e`
on `B`. Let `C` be a `K`-algebra that is a domain, `φ : B →ₐ[K] C` and `ψ : C` not a scalar. Then
no `h : B` satisfies `IsShift φ ψ h 1`.

Proof as implemented:

1. Choose `lam` with `lam ψ = 1` (`ψ ≠ 0`). Let `V = regularSpan {h}`. It is finite-dimensional,
   stable under right translation and contains `h`, and `regularSpan_le_shiftSubmodule` puts it
   inside the shifted elements. Choose a basis `b` of `V`.
2. `ρ0 = Chevalley.regularRepresentation e _ V b _`, with point matrices `evalAt x (M i j)` for
   `M = subspaceMatrix V b`. Let `ρ = ρ0.dual`, whose point matrices are inverse transposes.
3. The vector `ℓ i = shiftCoeff φ lam (b i)` is nonzero, since `h` has shift coefficient `1`. It is
   fixed by `ρ`: `sum_shiftCoeff_smul_subspaceMatrix` gives `ρ0(g)ᵀ ℓ = ℓ` on all points, and
   hence `(ρ0(g)⁻¹)ᵀ ℓ = ℓ`.
4. Geometric reductivity gives `P` homogeneous of degree `d > 0` with `P(ℓ) ≠ 0` and invariant
   under `ρ`. Evaluate the invariance at the inverse `u⁻¹` of the universal point `u = 𝟙` of
   `G'.X`, at the vector `ε₁ = (ε(b i))`. Here `ρ(u⁻¹) = ρ0(u)ᵀ`, and by
   `basis_eq_sum_counit` the vector `ρ0(u)ᵀ ε₁` is `(evalAt u (b j))`. Since `evalAt u` is
   injective (it is `(ΓSpecIso B).inv`), `P(b₁, …, b_m) = P(ε₁)` in `B`.
5. Applying `φ` and `IsShift.map_eq` gives `P(ε₁ + ψ ℓ) = P(ε₁)` in `C`. Then
   `HomogeneousShift.mem_range_of_aeval_shift` makes `ψ` a scalar, a contradiction.
