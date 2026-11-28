# Euclidean coordinates for field descent

This module constructs the Euclidean structure used for Arthur's descent of `(G, M)`-families
across a field extension (J. Arthur, *An introduction to the trace formula* (2005), Lemma 17.5,
printed pp.99–100, `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`), from purely
linear-algebraic data. The construction follows the usual choice of an invariant inner product:
the trace form of the adjoint representation, `Q(x, y) = Σ_γ m_γ γ(x) γ(y)` summed over the roots
with their multiplicities, which is invariant under the reflections, plus a positive form on the
central directions.

## Root sets from reflections

`isRootSet_of_reflections`: a finite set of nonzero vectors is a root set (`IsRootSet` of
[GMFamilies](GMFamilies.md)) if each `r` has a vector `v` with `⟪r, v⟫ = 2` such that
`x ↦ x - ⟪r, x⟫ v` is orthogonal, maps every element `s` of the set to `s - ⟪s, v⟫ r` inside the
set, and the pairings `⟪s, v⟫` are integers. Orthogonality forces `v = 2r/⟪r, r⟫`.

## The data

`FieldDescentData V₁ V` consists of

- an injective linear map `κ : V₁ → V` (the real cocharacters of the fine split component inside
  those of a maximal split torus);
- a finite set `roots` of nonzero functionals on `V` with positive multiplicities `mult`;
- for each root `γ` a coroot `γv` with `γ γv = 2` whose reflection `δ ↦ δ - δ(γv) γ` maps roots to
  roots, preserves multiplicities, and has integral pairings;
- `range_eq`: the image of `κ` is the common kernel of the roots that vanish on it (a Levi flat);
- complementary subspaces `B` and `K` of `V₁` (the coarse cocharacters and the common kernel of
  the coarse rational characters);
- `special`: for every root `γ` with nonzero restriction to `B`, the multiplicity-weighted sum of
  the roots having the same restriction to `B` as `γ`, composed with `κ`, vanishes on `K`.

## Construction

`ZT` is the common kernel of the roots and `Z₁ = κ⁻¹(ZT)`. The weighted fibre sums show that the
projections `πB`, `πK` along `B ⊕ K` preserve `Z₁` (`πB_mem_Z₁`, `πK_mem_Z₁`). Retractions `rB`,
`rK` onto `ZB = Z₁ ⊓ B` and `ZK = Z₁ ⊓ K` give the central components `pB`, `pK`; `ρ` is a left
inverse of `κ`, and `P = κ ∘ (pB + pK) ∘ ρ` is a projection of `V` onto `ZT` (`P_mem`, `P_of_mem`).

The coordinate map `F : V → EuclideanSpace ℝ Coord`, with `Coord` the roots together with two
copies of the coordinates of `V₁`, is `x ↦ (√(mult γ) γ(x))_γ ⊕ coords(pB(ρ x)) ⊕ coords(pK(ρ x))`.
`inner_F` computes `⟪F x, F y⟫ = Q(x, y) + ⟨pB ρ x, pB ρ y⟩ + ⟨pK ρ x, pK ρ y⟩` and `F_injective`
shows `F` is injective. With the modified coroots `coroot' γv = γv - P γv`,
`inner_F_reflection` shows that the reflections are orthogonal for this inner product.
`inner_F_B_K` shows that `κ(B)` and `κ(K)` are orthogonal: the cross term of `Q` regroups by
fibres of restriction to `B`, and each fibre sum vanishes on `K` by `special`; the central terms
vanish since `pB` kills `K` and `pK` kills `B`. `inner_F_central` shows that `x - pB x` is
orthogonal to the central directions for `x ∈ B`, so the orthogonal projection to the central
space preserves `B`.

## The Euclidean models

`E₀` is the range of `F`, with `eT : V ≃ₗ[ℝ] E₀`; `rv γ` is the Riesz vector of a functional and
`R₀` the image of the roots. `isRootSet_R₀` applies `isRootSet_of_reflections`. `e₁` identifies
`V₁` with `EuclideanSpace ℝ (Fin (finrank ℝ V₁))` isometrically for the restricted inner product
(`inner_e₁`), using an orthonormal basis of the range of `F ∘ κ`, and `φ` is the resulting
isometric embedding into `E₀` with `φ (e₁ x) = eT (κ x)` (`φ_e₁`).
