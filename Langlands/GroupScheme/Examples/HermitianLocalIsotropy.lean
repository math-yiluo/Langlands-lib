import Langlands.GroupScheme.Examples.HermitianNondegenerateCoordinates
import Langlands.GroupScheme.Examples.HermitianRootQuadraticForm
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Isotropy of Hermitian spaces over quadratic extensions of local fields -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HermitianRoot

open Module SU3Root

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {V : Type v} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
  (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)

/-- Over a separable quadratic extension of a nonarchimedean local field, an
anisotropic diagonal Hermitian form has at most two coordinates. -/
theorem DiagonalForm.card_le_two_of_isAnisotropic {ι : Type v} [Fintype ι]
    (H : DiagonalForm (fieldInvolution K L) ι) (hH : H.IsAnisotropic) :
    Fintype.card ι ≤ 2 := by
  have : FiniteDimensional K L :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]; decide)
  have hq := localQuadraticAnisotropicDimensionBound K (ι → L) (H.quadraticForm K L)
    ((H.quadraticForm_anisotropic_iff K L).mpr hH)
  rw [DiagonalForm.quadraticForm_finrank] at hq
  omega

include hbar in
/-- Over a separable quadratic extension of a nonarchimedean local field, an
anisotropic Hermitian space has dimension at most two. -/
theorem local_anisotropic_finrank_le_two (ha : ∀ x, h x x = 0 → x = 0) :
    finrank L V ≤ 2 := by
  obtain ⟨H, hH, -, -⟩ := exists_anisotropic_diagonal_coordinates h hbar ha
  simpa using H.card_le_two_of_isAnisotropic hH

include hbar in
/-- Over a separable quadratic extension of a nonarchimedean local field, every
Hermitian space of dimension at least three has a nonzero isotropic vector. -/
theorem local_exists_isotropic (hdim : 3 ≤ finrank L V) :
    ∃ x : V, x ≠ 0 ∧ h x x = 0 := by
  by_contra! hne
  have hle := local_anisotropic_finrank_le_two h hbar (fun x hx => by
    by_contra hx0
    exact hne x hx0 hx)
  omega

include hbar in
/-- Over a separable quadratic extension of a nonarchimedean local field, a
nondegenerate Hermitian space of dimension `m + 2` with `1 ≤ m` has explicit linear
coordinates with one hyperbolic plane and a negative diagonal middle on `Fin m` whose
weights are nonzero. -/
theorem local_exists_hyperbolic_diagonal_coordinates (hn : h.Nondegenerate)
    (m : ℕ) (hm : 1 ≤ m) (hdim : finrank L V = m + 2) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), (∀ i, H.weight i ≠ 0) ∧
      ∃ e : V ≃ₗ[L] L × ((Fin m → L) × L), ∀ v w,
        h v w = (e v).1 * (fieldInvolution K L).bar (e w).2.2 -
          H.pairing (e v).2.1 (e w).2.1 +
          (e v).2.2 * (fieldInvolution K L).bar (e w).1 := by
  obtain ⟨x, hx, hxx⟩ := local_exists_isotropic h hbar (by omega)
  exact exists_isotropic_diagonal_coordinates hbar hn hx hxx m hdim

include hbar in
/-- Over a separable quadratic extension of a nonarchimedean local field, a
nondegenerate Hermitian space of dimension `m + 2` with `1 ≤ m` has a basis indexed by
`Index (Fin m)` whose Gram matrix is `gram H` for a diagonal form `H` with nonzero
weights. -/
theorem local_exists_gram_basis (hn : h.Nondegenerate) (m : ℕ) (hm : 1 ≤ m)
    (hdim : finrank L V = m + 2) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), (∀ i, H.weight i ≠ 0) ∧
      ∃ b : Basis (Index (Fin m)) L V, ∀ i j, h (b i) (b j) = gram H i j := by
  obtain ⟨x, hx, hxx⟩ := local_exists_isotropic h hbar (by omega)
  exact exists_isotropic_gram_basis hbar hn hx hxx m hdim

/-- Over a separable quadratic extension of a nonarchimedean local field, every
Hermitian matrix `M` indexed by `Index (Fin m)` with `1 ≤ m` and nonzero determinant is
congruent to `gram H` for a diagonal form `H` with nonzero weights: there is an
invertible `P` with `Pᴴ M P = gram H`. -/
theorem local_exists_gram_congruence (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Index (Fin m)) (Index (Fin m)) L)
    (hM : conjugateTranspose (fieldInvolution K L) M = M) (hdet : M.det ≠ 0) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), (∀ i, H.weight i ≠ 0) ∧
      ∃ P : Matrix.GeneralLinearGroup (Index (Fin m)) L,
        conjugateTranspose (fieldInvolution K L)
            (P : Matrix (Index (Fin m)) (Index (Fin m)) L) * M *
          (P : Matrix (Index (Fin m)) (Index (Fin m)) L) = gram H := by
  have hM' : ∀ k l, (fieldInvolution K L).bar (M k l) = M l k := fun k l =>
    congrFun (congrFun hM l) k
  have hdim : finrank L (Index (Fin m) → L) = m + 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    omega
  obtain ⟨H, hH, b, hb⟩ := local_exists_gram_basis (matrixHermitianPairing K M)
    (matrixHermitianPairing_bar hM') (matrixHermitianPairing_nondegenerate hM' hdet)
    m hm hdim
  let e := Pi.basisFun L (Index (Fin m))
  refine ⟨H, hH, ⟨e.toMatrix b, b.toMatrix e, e.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip e⟩, ?_⟩
  have hcol : ∀ j, (fun k => e.toMatrix b k j) = b j := fun j =>
    funext fun k => by simp [e, Basis.toMatrix_apply]
  ext i j
  change (conjugateTranspose (fieldInvolution K L) (e.toMatrix b) * M * e.toMatrix b) i j =
    gram H i j
  rw [conjugateTranspose_mul_mul_apply, hcol, hcol, hb, gram_apply_comm]

end Langlands.GroupScheme.HermitianRoot
