# The isometry group of the descended involution through a split orthogonal chart

Author: Worker 1383, for Task 6507 (`f0045927-f50c-4853-9944-3c98c7ea5daf`), in collaboration
with Worker 74. This module is the orthogonal counterpart of `SymplecticInnerForm/NormOneChart`
and uses the extended charts `chartAlong` and point scalars `pointScalars` of
`SpecialLinearInnerForm/NormOneChart`. All declarations are in the namespace
`Langlands.GroupScheme.EvenOrthogonalForm`. Notation as in `Similitude` and `TwistedAlgebra`:
for a finite type `l` and a commutative ring `R`, `τ₀ = orthogonalInvolution R l` is
`x ↦ J xᵀ J` on `M_{l ⊕ l}(R)`, `Alt τ₀ = {y - τ₀ y}`, `p = leftProjection R l`, and
`orthogonalGroup l R` is the group of matrices `X` with `X Q Xᵀ - Q` alternating.

## Matrix lemmas

- `mul_mul_orthogonalInvolution_mem`: if `W ∈ Alt τ₀`, then `X W τ₀(X) ∈ Alt τ₀` for every
  matrix `X`. For `W = V - τ₀ V`, the product is `U - τ₀ U` with `U = X V τ₀(X)`.
- `map_mem_alternatingSubspace`: applying a ring homomorphism to the entries preserves `Alt τ₀`
  (`orthogonalInvolution_map`).
- `defect_mem_alternatingSubspace_iff hP X`: if `P - p ∈ Alt τ₀`, then
  `X P τ₀(X) - P ∈ Alt τ₀ ↔ X ∈ orthogonalGroup l R`. The two defects for `P` and `p` differ
  by `X (P - p) τ₀(X) - (P - p)`, which lies in `Alt τ₀` by the first lemma. So the statement
  reduces to the case `P = p`, which is `mem_orthogonalGroup_iff_projection`.

## The chart along a coefficient map

Fix a field `K`, a `K`-algebra `A` with an involution of the first kind `τ`, a field `L` over
`K`, and a chart `ε : L ⊗[K] A ≃ₐ[L] M_{l ⊕ l}(L)` with
`he : ∀ x, ε (τ_L x) = τ₀ (ε x)` (`τ_L = τ.baseChange L`). Let `R` be a commutative `K`-algebra
and `f : L →+* R` with `hf : f ∘ algebraMap K L = algebraMap K R`. Write
`χ = chartAlong ε f hf : R ⊗[K] A →ₐ[R] M_{l ⊕ l}(R)`, so `χ (r ⊗ a) = r · f(ε(1 ⊗ a))`.
It is bijective (`chartAlong_bijective`).

- `chartAlong_baseChange ε he f hf x`: `χ (τ_R x) = τ₀ (χ x)`. On pure tensors this is `he`
  mapped entrywise by `f` (`orthogonalInvolution_map`). Additivity gives the general case.
- `mem_alternatingSubspace_baseChange_iff`: `y ∈ R ⊗ {a - τ a}` if and only if `χ y ∈ Alt τ₀`.
  The base-changed subspace is `{z - τ_R z}` (`IsometryCut.alternatingSubspace_baseChange`).
  Surjectivity and injectivity of `χ` transfer this description.
- `chartAlong_defect ε he f hf a₀ y`: with
  `IsometryCut.defect τ a₀ y = y (1 ⊗ a₀) τ_R(y) - 1 ⊗ a₀`, we have
  `χ (defect τ a₀ y) = χ(y) P τ₀(χ y) - P` for `P = f(ε(1 ⊗ a₀))`.
- `defect_mem_iff ε he f hf ha₀ y`: assume `ha₀ : ε(1 ⊗ a₀) - p ∈ Alt τ₀` (over `L`). Then
  `defect τ a₀ y ∈ R ⊗ {a - τ a}` if and only if `χ y ∈ orthogonalGroup l R`. The hypothesis
  maps by `f` to `P - p ∈ Alt τ₀` over `R`. Combine the two previous items with
  `defect_mem_alternatingSubspace_iff`.
- `chartIsometryEquiv ε he f hf ha₀`: a group isomorphism from
  `IsometryCut.isometrySubgroup isStable_alternatingSubspace a₀ R` to `orthogonalGroup l R`.
  The source is the subgroup of units `u` of `R ⊗[K] A` with
  `u (1 ⊗ a₀) τ_R(u) - 1 ⊗ a₀ ∈ R ⊗ {a - τ a}`. A unit goes to its chart matrix, and the inverse
  applies the inverse of the algebra isomorphism `χ` to the unit `toGL X`. By
  `chartIsometryEquiv_coe` (by `rfl`), the underlying matrix of the image of `u` is `χ u`.

## The local isomorphism over the points of `Spec L`

Assume `A` finite-dimensional. Let `V` be a relative test scheme over `Spec K` with global
sections `R_V = ((algΓ K).obj V).unop`.

- `cutPointsEquiv τ a₀ V`: the points `V ⟶ G` of
  `G = IsometryCut.groupScheme isStable_alternatingSubspace a₀` are the isometry units over
  `R_V`. This is `Corepresented.pointsEquiv` for the cut-out description
  `IsometryCut.isCutOutBy`. `cutPointsEquiv_naturality`: restricting a point along `t : W ⟶ V`
  maps its unit by the pullback of global sections (`Algebra.TensorProduct.map`).
- `chartPoints ε he ha₀ s`, for `s : V ⟶ ringTest K L` (a point of `Spec L` over `Spec K`):
  `cutPointsEquiv` followed by `chartIsometryEquiv` along `f = pointScalars s`. By
  `chartPoints_coe` (by `rfl`), its matrix is `chartAlong ε (pointScalars s) _` of the unit.
  `chartPoints_naturality`: for `t : W ⟶ V`, the chart point of `t ≫ x` along `t ≫ s` is the
  chart point of `x` along `s`, mapped by `t` on global sections. The proof combines
  `cutPointsEquiv_naturality`, `chartAlong_naturality` and `pointScalars_comp`.
- `chartLocalIso ε he ha₀ : LocalGroupIso G (OrthogonalMatrix.groupScheme l K) (ringTest K L)`
  sends `s` to `chartPoints ε he ha₀ s` followed by the inverse of
  `OrthogonalMatrix.pointsEquiv`. Naturality follows from `chartPoints_naturality` and
  `OrthogonalMatrix.pointsEquiv_naturality`. `pointsEquiv_chartLocalIso`: the orthogonal matrix
  of the image of `x` is `chartPoints ε he ha₀ s x`.

## The twisted fixed algebra and its Galois law

Now take the setting of `TwistedAlgebra`: a finite Galois extension `N/K`, a family
`g : Gal(N/K) → GL_{2n}(N)` with `hcoc` (the twisted action law) and `hsim` (every `g_σ` is a
similitude). Let `A` be the fixed algebra of `twistedAction g hcoc`, with
`τ = descendedInvolution g hcoc hsim`, `a₀ = basePoint g hcoc` and
`ε = descentEquiv : N ⊗[K] A ≃ₐ[N] M_{2n}(N)`.

- `chartAlong_galois g hcoc f hf σ hf' x`: along the coefficient map `f ∘ σ`, the chart of
  `x : R ⊗[K] A` is `f(g_σ) (chartAlong ε f hf x) f(g_σ⁻¹)`. On pure tensors this is
  `map_galois_fixed` (`σ(a) = g_σ a g_σ⁻¹` for fixed `a`) mapped by `f`. Additivity gives the
  general case.
- `descentEquiv_basePoint_sub_mem`: `ε(1 ⊗ a₀) - p ∈ Alt τ₀`, which is `basePoint_sub_mem`
  (here `ε(1 ⊗ a) = a`).
- `twistedChartLocalIso g hcoc hsim` is `chartLocalIso` for these data. It is a local
  isomorphism, over the points of `Spec N`, from `IsometryCut.groupScheme` of `(A, τ, a₀)` to
  the split orthogonal group scheme `OrthogonalMatrix.groupScheme (Fin n) K`.
- `pointsEquiv_twistedChartLocalIso`: the orthogonal matrix of the image of `x` at `s`, as a
  matrix over `Γ(V.left, ⊤)`, is `chartAlong ε (pointScalars s) _` of the isometry unit of `x`.
- `chartScalars s` is `pointScalars s`, with its codomain written as `Γ(V.left, ⊤)` so that it
  can multiply the matrices of `OrthogonalMatrix.pointsEquiv`.
- `twistedChartLocalIso_galois σ s x` (**Galois law**): at the point `s ≫ ringTestMap K σ` the
  matrix is `g_σ' M g_σ'⁻¹`, where `M` is the matrix at `s` and `'` maps entries by
  `chartScalars s`. Since `pointScalars (s ≫ ringTestMap K σ) = pointScalars s ∘ σ`
  (`pointScalars_comp_ringTestMap`), this is `chartAlong_galois`.
- `exists_twistedChart g hcoc hsim` (for `NeZero n`) packages these data. There are a central
  simple `K`-algebra `A` with an involution `τ` and an `N`-algebra isomorphism
  `e : N ⊗[K] A ≃ₐ[N] M_{2n}(N)` with `e(τ_N x) J = J e(x)ᵀ`, an element `a₀` with
  `a₀ + τ a₀ = 1`, and a local isomorphism `χ` from `IsometryCut.groupScheme` of `(A, τ, a₀)` to
  the split orthogonal group over `Spec N` that obeys the Galois law above.

No hypothesis on the characteristic of `K` is used.

## Provenance

Derived. Over a splitting field, the isometry group of the twisted algebra with involution and
base point becomes the split orthogonal group. The Galois law records that the comparison
differs between conjugate points by the cocycle. This is the standard Galois-descent
description of forms of `O_{2n}` in M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The
Book of Involutions* (AMS Colloquium Publications 44, 1998; source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`), §29.F, printed pp.408–409 /
PDF pp.431–432. The algebraic content is the matrix fact `defect_mem_alternatingSubspace_iff`:
through the chart, the isometry condition for the quadratic pair `(τ₀, [P])`, with `P` congruent
to `p` modulo `Alt τ₀`, is orthogonality for the split hyperbolic form (KMRT §5.B). The
construction follows the Library modules `SymplecticInnerForm/NormOneChart` and
`SpecialLinearInnerForm/NormOneChart`.
