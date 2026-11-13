import Langlands.GroupScheme.Examples.HermitianHyperbolicMatrixCoordinates
import Langlands.GroupScheme.Examples.HermitianRootUnitWitnesses
import Mathlib.Data.ENat.Basic

/-! # Rectangular matrix coordinates for rank-one Hermitian spaces -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

variable {A : Type u} [CommRing A] {ι : Type v} {κ : Type w}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The matrix of a coordinate equivalence between possibly different finite
index types. Its rows are indexed by the target and columns by the source. -/
def rectangularCoordinateMatrix (e : (ι → A) ≃ₗ[A] (κ → A)) : Matrix κ ι A :=
  LinearMap.toMatrix' e.toLinearMap

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem rectangularCoordinateMatrix_apply
    (e : (ι → A) ≃ₗ[A] (κ → A)) (i : κ) (j : ι) :
    rectangularCoordinateMatrix e i j = e (Pi.single j 1) i := rfl

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem rectangularCoordinateMatrix_mulVec
    (e : (ι → A) ≃ₗ[A] (κ → A)) (z : ι → A) :
    (rectangularCoordinateMatrix e).mulVec z = e z :=
  LinearMap.toMatrix'_mulVec e.toLinearMap z

/-- The matrices of the two directions multiply to the target identity. -/
@[simp] theorem rectangularCoordinateMatrix_mul_symm
    (e : (ι → A) ≃ₗ[A] (κ → A)) :
    rectangularCoordinateMatrix e * rectangularCoordinateMatrix e.symm = 1 := by
  rw [rectangularCoordinateMatrix, rectangularCoordinateMatrix,
    ← LinearMap.toMatrix'_comp]
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact e.apply_symm_apply z
  rw [he, LinearMap.toMatrix'_id]

/-- The reverse product is the source identity. -/
@[simp] theorem rectangularCoordinateMatrix_symm_mul
    (e : (ι → A) ≃ₗ[A] (κ → A)) :
    rectangularCoordinateMatrix e.symm * rectangularCoordinateMatrix e = 1 :=
  rectangularCoordinateMatrix_mul_symm e.symm

omit [DecidableEq κ] in
/-- Full pairing coordinates between distinct finite index types give the
actual rectangular Gram congruence. -/
theorem rectangularGramCongruence_of_pairing_coordinates
    (c : RingInvolution A) (J : Matrix ι ι A) (B : Matrix κ κ A)
    (e : (ι → A) ≃ₗ[A] (κ → A))
    (he : ∀ z w, dotProduct (fun i => c.bar (w i)) (J.mulVec z) =
      dotProduct (fun i => c.bar (e w i)) (B.mulVec (e z))) :
    ((rectangularCoordinateMatrix e).map c.bar).transpose * B *
      rectangularCoordinateMatrix e = J := by
  ext i j
  calc
    _ = dotProduct (fun k => c.bar (e (Pi.single i 1) k))
        (B.mulVec (e (Pi.single j 1))) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        rectangularCoordinateMatrix_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = dotProduct (fun k => c.bar ((Pi.single i (1 : A) : ι → A) k))
        (J.mulVec (Pi.single j 1)) := (he (Pi.single j 1) (Pi.single i 1)).symm
    _ = J i j := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {V : Type v} [AddCommGroup V] [Module L V] [FiniteDimensional L V]

/-- An attained maximal isotropic dimension of one supplies genuine Gram
coordinates and units for the negative anisotropic diagonal middle. -/
theorem exists_rankOne_attained_gram_coordinates
    (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
    (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)
    (hn : h.Nondegenerate)
    (hatt : ∃ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) ∧ (Module.finrank L W : ℕ∞) = 1)
    (hbound : ∀ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) → (Module.finrank L W : ℕ∞) ≤ 1)
    (m : ℕ) (hdim : Module.finrank L V = m + 2) :
    ∃ (H : DiagonalForm (fieldInvolution K L) (Fin m))
      (w : Fin m → Lˣ) (_hw : ∀ i, (w i : L) = H.weight i),
      H.IsAnisotropic ∧ ∃ e : V ≃ₗ[L] (Index (Fin m) → L), ∀ z t,
        h z t = dotProduct (fun i => (fieldInvolution K L).bar (e t i))
          ((gram H).mulVec (e z)) := by
  obtain ⟨W, hW, hWdim⟩ := hatt
  have hWdim' : Module.finrank L W = 1 := by exact_mod_cast hWdim
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := L) (M := W)).mp
    (by omega)
  have hx' : (x : V) ≠ 0 := by
    intro hz
    exact hx (Subtype.ext hz)
  have hbound' (U : Submodule L V)
      (hU : ∀ a b : U, h (a : V) (b : V) = 0) : Module.finrank L U ≤ 1 := by
    exact_mod_cast hbound U hU
  obtain ⟨H, hH, e, he⟩ :=
    exists_rankOne_gram_coordinates h hbar hn hx' (hW x x) hbound' m hdim
  obtain ⟨w, hw⟩ := H.exists_unitWitnesses hH
  exact ⟨H, w, hw, hH, e, he⟩

/-- The attained rank-one hypothesis on a finite source yields two-sided
matrix coordinates with exactly the middle size required by the outer-A model. -/
theorem exists_rankOne_finiteSource_gram_coordinates
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hnat : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    (h : (ι → L) →ₗ[L] (ι → L) →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
    (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)
    (J : Matrix ι ι L)
    (hJ : ∀ z t, h z t =
      dotProduct (fun i => (fieldInvolution K L).bar (t i)) (J.mulVec z))
    (hn : h.Nondegenerate)
    (hatt : ∃ W : Submodule L (ι → L),
      (∀ a b : W, h (a : ι → L) (b : ι → L) = 0) ∧
        (Module.finrank L W : ℕ∞) = 1)
    (hbound : ∀ W : Submodule L (ι → L),
      (∀ a b : W, h (a : ι → L) (b : ι → L) = 0) →
        (Module.finrank L W : ℕ∞) ≤ 1) :
    ∃ (H : DiagonalForm (fieldInvolution K L) (Fin (n - 1)))
      (w : Fin (n - 1) → Lˣ) (_hw : ∀ i, (w i : L) = H.weight i),
      H.IsAnisotropic ∧
      ∃ e : (ι → L) ≃ₗ[L] (Index (Fin (n - 1)) → L),
        (∀ z t, h z t = dotProduct (fun i => (fieldInvolution K L).bar (e t i))
          ((gram H).mulVec (e z))) ∧
        rectangularCoordinateMatrix e * rectangularCoordinateMatrix e.symm = 1 ∧
        rectangularCoordinateMatrix e.symm * rectangularCoordinateMatrix e = 1 ∧
        ((rectangularCoordinateMatrix e).map (fieldInvolution K L).bar).transpose *
          gram H * rectangularCoordinateMatrix e = J := by
  have hdim : Module.finrank L (ι → L) = (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
    omega
  obtain ⟨H, w, hw, hH, e, he⟩ :=
    exists_rankOne_attained_gram_coordinates h hbar hn hatt hbound (n - 1) hdim
  refine ⟨H, w, hw, hH, e, he, rectangularCoordinateMatrix_mul_symm e,
    rectangularCoordinateMatrix_symm_mul e, ?_⟩
  apply rectangularGramCongruence_of_pairing_coordinates
  intro z t
  exact (hJ z t).symm.trans (he z t)

end Langlands.GroupScheme.HermitianRoot
