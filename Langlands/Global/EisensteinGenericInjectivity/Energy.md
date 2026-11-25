# Invariant archimedean energies from an invariant positive definite Hermitian form

Module `Langlands.Global.EisensteinGenericInjectivity.Energy` gives, for a matrix
representation `σ` of `G`, an infinite place `w` and a compact subgroup `K` of `G(𝔸)`, an
invariant energy in the sense of `IsInvariantEnergy` (module
`Langlands.Global.EisensteinGenericInjectivity.PlaceHeight`) that is moreover a real quadratic
expression (`exists_quadraticEnergy`). The energy is the Hermitian form of a positive definite
matrix invariant under `σ_w(K)`, obtained from the Library theorem
`Langlands.Group.DenseCompactForm.exists_posDef_invariant` (module
`Langlands.GroupScheme.MatrixRepresentationDenseCompact`). The module
`Langlands.Global.EisensteinGenericInjectivity.Separation` uses these energies at every
infinite place.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`, for a number field `F`; `σ_w(x) = placeMatrix σ w x`. Complete types are printed by
`PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the page of
`Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `continuous_placeMatrix`: `σ_w : G(𝔸) → M_N(ℂ)` is continuous.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.continuous_placeMatrix.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) : Continuous (placeMatrix σ w)
  ```
- `IsQuadraticEnergy σ w K Q B` is a structure in `Prop` extending `IsInvariantEnergy σ w K Q`
  by the field `expand`: for real coefficients `a`,
  `Q(∑_r a_r y_r) = ∑_{r,s} a_r a_s B(y_r, y_s)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsQuadraticEnergy.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (K : Subgroup (AdelicGroupPoints F G))
    (Q : (Fin N → ℂ) → ℝ) (B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ) : Prop
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsQuadraticEnergy.toIsInvariantEnergy.{u} {F : Type u}
    [Field F] [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ}
    {σ : G.MatrixRepresentation (Fin N)} {w : Langlands.Global.InfinitePlace F}
    {K : Subgroup (AdelicGroupPoints F G)} {Q : (Fin N → ℂ) → ℝ} {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ}
    (self : IsQuadraticEnergy σ w K Q B) : IsInvariantEnergy σ w K Q
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsQuadraticEnergy.expand.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)}
    {w : Langlands.Global.InfinitePlace F} {K : Subgroup (AdelicGroupPoints F G)}
    {Q : (Fin N → ℂ) → ℝ} {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} (self : IsQuadraticEnergy σ w K Q B)
    (n : ℕ) (a : Fin n → ℝ) (y : Fin n → Fin N → ℂ) :
    Q (∑ r, ↑(a r) • y r) = ∑ r, ∑ s, a r * a s * B (y r) (y s)
  ```
- `exists_quadraticEnergy`: for every `σ`, infinite place `w` and compact subgroup `K` of
  `G(𝔸)` there are `Q` and `B` with `IsQuadraticEnergy σ w K Q B`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exists_quadraticEnergy.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} [IsAffine G.X.left]
    (σ : G.MatrixRepresentation (Fin N)) (w : Langlands.Global.InfinitePlace F)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsCompact ↑K) : ∃ Q B, IsQuadraticEnergy σ w K Q B
  ```

## Proofs

- `continuous_placeMatrix`: each entry is `placeHom w` applied to an entry of the continuous
  `adelicMatrix F G σ`.
- `exists_quadraticEnergy`. Let `ρ : G(𝔸) → GL_N(ℂ)` be `adelicMatrix F G σ` followed by
  `Matrix.GeneralLinearGroup.map (placeHom w)`; its underlying matrix is `σ_w`. It is continuous
  (`Units.continuous_iff`: the matrix and the matrix of the inverse, `σ_w(x⁻¹)`, are
  continuous), so `ρ(K)` is a compact subgroup of `GL_N(ℂ)`.
  `DenseCompactForm.exists_posDef_invariant` gives a positive definite `J` with
  `ρ(k)* J ρ(k) = J` for `k ∈ K`; in that module `J` is the Haar average over `ρ(K)` of the
  pulled-back standard Hermitian forms. Put

  `Q(z) = Re (z* J z)` and `B(y, y') = Re (y'* J y)`.

  - Positivity: `z* J z > 0` for `z ≠ 0` (`Matrix.PosDef.dotProduct_mulVec_pos`).
  - Homogeneity: `(c z)* J (c z) = |c|² z* J z`.
  - Invariance: `(σ_w(k) z)* J σ_w(k) z = z* (σ_w(k)* J σ_w(k)) z = z* J z` for `k ∈ K`.
  - Expansion: `(∑_r a_r y_r)* J (∑_r a_r y_r) = ∑_{r,s} a_r a_s y_s* J y_r` for real `a`.

## Sources

Averaging a Hermitian form over a compact group is the construction of the Library module
`Langlands.GroupScheme.MatrixRepresentationDenseCompact`; its page gives the literature. No
further source.
