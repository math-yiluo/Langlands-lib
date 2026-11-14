# Orthogonal involutions are adjoint to hermitian division forms

Author: Worker 1383, for Task 6507 (`f0045927-f50c-4853-9944-3c98c7ea5daf`), in collaboration
with Worker 74. This module is the orthogonal counterpart of the published
`SymplecticInnerForm/SymplecticInvolutionAntihermitian` and reuses its auxiliary results.

## Main result

`Langlands.GroupScheme.OrthogonalInnerForm.orthogonalInvolutionHermitian`.

Let `K` be a field and `A` a finite-dimensional central simple `K`-algebra (both in universe
`u`) with an involution of the first kind `τ`. Let `L` be a field over `K` (in universe `u`)
and `e : L ⊗[K] A ≃ₐ[L] M_{2n}(L)` an `L`-algebra isomorphism, with matrices indexed by
`Fin n ⊕ Fin n`. Assume

`e (τ_L x) * J = J * (e x)ᵀ` for every `x : L ⊗[K] A`,

where `J = Langlands.GroupScheme.OrthogonalMatrix.polarMatrix (Fin n) L` is the symmetric
block matrix `[[0, 1], [1, 0]]` (the polar matrix of the split quadratic form). Then there are:

- natural numbers `degree` and `m` with `m ≠ 0` (`NeZero m`), `0 < degree` and
  `m * degree = 2 * n`;
- a central division `K`-algebra `D` in universe `u`, finite-dimensional over `K`, with
  `finrank K D = degree ^ 2`;
- an involution of the first kind `σ` of `D` whose symmetric subspace has dimension
  `degree * (degree + 1) / 2`;
- a matrix `H ∈ M_m(D)` that is `σ`-hermitian (`σ.matrix (Fin m) H = H`, i.e. `ᵗH^σ = H`) and
  invertible (`IsUnit H`);
- a `K`-algebra isomorphism `φ : A ≃ₐ[K] M_m(D)` with `φ (τ x) * H = H * σ.matrix (Fin m) (φ x)`
  for every `x : A`.

So `φ` carries `τ` to the adjoint involution `y ↦ H ᵗy^σ H⁻¹` of the hermitian matrix `H`.
The conclusion has the same shape as `SymplecticInvolutionAntihermitianStatement`. The
difference is that `H` is hermitian instead of trace-valued antihermitian. The symmetric
dimension `d(d + 1)/2` says that `σ` is orthogonal when `2 ≠ 0` in `K`. In characteristic two
it carries no type information, because there symmetric and skew elements coincide.

## Auxiliary results

In the namespace `Langlands.GroupScheme.Quaternionic.FirstKindInvolution`:

- `map_polarChart_eq τ e he x`: from the hypothesis and `J * J = 1`
  (`OrthogonalMatrix.polarMatrix_mul_self`), `e (τ_L x) = J * (e x)ᵀ * J`.
- `finrank_epsSymmetric_one_scalarInvolution L`: for the identity involution
  `Symplectic.scalarInvolution L` of a field `L`, every element is `1`-symmetric, so the
  space has dimension `1`.
- `finrank_symmetricSubspace_of_polarChart τ e he`:
  `finrank K τ.symmetricSubspace = 2 * n + (2 * n).choose 2`. Proof: pass to `L` by the
  published `finrank_symmetricSubspace_baseChange` and transport along `e`
  (`epsSymmetricCongr`). The transported involution is `y ↦ J ᵗy J`, which is the Gram
  construction for `θ = scalarInvolution L` with `H = H' = J` and `ε = 1`, since `ᵗJ = J`
  (`polarMatrix_transpose`). The published `finrank_symmetricSubspace_eq_of_gram` identifies
  its symmetric elements with the symmetric `L`-matrices of size `2n`, and
  `finrank_epsSymmetric_matrix` counts them as `2n · 1 + (2n choose 2)`.
- `exists_isGramModel_signFlip τ` for an involution of the first kind `τ` of `M_ι(D)`, with
  `ι` nonempty: there is a Gram model `IsGramModel τ θ ε U U'` such that every nonzero
  `v : D` with `θ v = -v` gives another Gram model `IsGramModel τ θ' (-ε) U₂ U₂'` of opposite
  sign. Proof: build the model from a corner `x` at a fixed index `i₀`
  (`exists_isCorner_eps`, `exists_cornerData`), with corner datum `c`. The element
  `single i₀ i₀ v * c.w` is again a corner. It is nonzero, because multiplying it on the left
  by `single i₀ i₀ v⁻¹` recovers `c.w`. Using `c.map_w`, `c.w_mul_map_single` and `θ v = -v`,
  it satisfies `τ y = (-ε) • y`. A second application of `exists_cornerData` then produces a
  model of sign `-ε`. The published `exists_isGramModel` makes the same sign change in the
  opposite direction (from `+1` to `-1`); this lemma uses its corner argument.

In the namespace `Langlands.GroupScheme.OrthogonalInnerForm` (public restatements of
arithmetic lemmas that are private in the symplectic module):

- `choose_two_mul m d : (m * d).choose 2 = m * d.choose 2 + m.choose 2 * (d * d)`, proved by
  casting to `ℚ`.
- `eq_of_finrank_count`: if `0 < m`, `m * d = N` and
  `m * s + m.choose 2 * (d * d) = N + N.choose 2`, then `s = d + d.choose 2`.
- `mul_succ_div_two d : d * (d + 1) / 2 = d + d.choose 2`.

## Proof of the main theorem

1. **Wedderburn.** `A` is artinian, so `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`
   gives `m ≠ 0`, a finite-dimensional division `K`-algebra `D` and `φ : A ≃ₐ[K] M_m(D)`.
   `CentralSimple.isCentral_of_algEquiv_matrix` makes `D` central. Let
   `d = CentralSimple.reducedDegree K D`; then `finrank K D = d * d` and `0 < d`.
2. **Degree.** `finrank K A = (2n)²` by base change along `e`, and `finrank K A = (m d)²` by
   `φ`. Hence `m d = 2n`.
3. **Counting.** Let `τ_B = τ.algEquivCongr φ`. It has the same symmetric dimension as `τ`,
   which is `2n + (2n choose 2)` by `finrank_symmetricSubspace_of_polarChart`. For any Gram
   model `(θ, ε, U, U')` of `τ_B`, `IsGramModel.finrank_symmetricSubspace` gives
   `m · dim (θ-ε-symmetric) + (m choose 2) d² = 2n + (2n choose 2)`. So
   `eq_of_finrank_count` gives `dim (θ-ε-symmetric) = d + (d choose 2)`.
4. **A model with sign `1`.** `exists_isGramModel_signFlip τ_B` gives a model with sign `ε`,
   where `ε * ε = 1`.
   - If `(2 : K) = 0`, then `(ε - 1)² = 0`, so `ε = 1`.
   - Otherwise `ε = 1` or `ε = -1`. If `ε = -1`, step 3 shows that the skew elements of `θ`
     have dimension `d + (d choose 2) > 0`. Pick a nonzero `v` with `θ v = -v`. The
     sign-change clause gives a model of sign `-(-1) = 1`.

   Fix a model `(θ, 1, U, U')`. Step 3 gives `dim Sym θ = d + (d choose 2) = d(d + 1)/2`.
5. **Conclusion.** Take `degree = d`, `m`, `D`, `σ = θ` and `H = U`. Hermitian: `ᵗU^θ = 1 • U`
   is part of the model. `U` is a unit with inverse `U'`. For `x : A`,
   `τ_B (φ x) = φ (τ x)`, so `φ (τ x) * U = U * ᵗ(φ x)^θ * U' * U = U * ᵗ(φ x)^θ`.

## Provenance

Provenance: derived. The statement specializes M.-A. Knus, A. Merkurjev, M. Rost and
J.-P. Tignol, *The Book of Involutions* (AMS Colloquium Publications 44, 1998; source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`), Theorem (4.2)(1) (printed p.43,
PDF p.66) to involutions that become adjoint to a symmetric form over a splitting field, with
division coefficient algebras. KMRT state (4.2) for `ε`-hermitian forms; here the sign is
fixed to `+1` (hermitian). As in the published symplectic module, the proof does not use
KMRT's route through Proposition (2.20) and reduced traces. It compares symmetric dimensions
with the split model given by `e` (KMRT's computation before Definition (2.5), printed p.16,
PDF p.39) and changes the sign of the corner construction by a skew element of `θ`.
