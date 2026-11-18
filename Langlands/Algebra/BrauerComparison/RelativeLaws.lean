import Langlands.Algebra.BrauerComparison.Relative
import Langlands.Algebra.BrauerGroup

/-! # Matrix stability and tensor addition for relative Brauer classes -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u v w

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local (relativeCohomology)
open CentralSimple CentralSimple.SemilinearGaloisAction

attribute [local instance] coefficientGLAction

variable {K L A B : Type u} [Field K] [Field L] [Algebra K L]
  [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
  {J : Type w} [Fintype J] [DecidableEq J] [Nonempty J]

/-- Reindexing a matrix chart transports its lifts and keeps its unit factors. -/
theorem relativeClass_reindex (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (r : I ≃ J) :
    relativeClass (e.trans (Matrix.reindexAlgEquiv L L r)) = relativeClass e := by
  let ρ := splittingChartIndexAction e
  let R := Matrix.reindexAlgEquiv L L r
  let m : GL I L →* GL J L := Units.map R.toRingHom.toMonoidHom
  have hm (s : Gal(L/K)) (P : GL I L) : m (s • P) = s • m P := by
    apply Units.ext
    ext i j
    rfl
  have hscalar (a : Lˣ) : m (GeneralLinearGroup.scalar I a) = GeneralLinearGroup.scalar J a := by
    apply Units.ext
    exact R.commutes (a : L)
  have hmul (s t : Gal(L/K)) : m (ρ.innerMatrix s) * (s • m (ρ.innerMatrix t)) =
      GeneralLinearGroup.scalar J (ρ.scalarDefect s t) * m (ρ.innerMatrix (s * t)) := by
    rw [← hm, ← map_mul, ρ.innerMatrix_mul, map_mul, hscalar]
  apply descentClass_eq_of_lifts _ (m ∘ ρ.innerMatrix) ρ.scalarDefect _ hmul
  intro s X
  obtain ⟨Y, rfl⟩ := (e.trans R).surjective X
  rw [splittingChartIndexAction_apply]
  change R (e (tensorCoefficientMap s Y)) =
    (m (ρ.innerMatrix s) : Matrix J J L) * (R (e Y)).map s *
      (((m (ρ.innerMatrix s))⁻¹ : GL J L) : Matrix J J L)
  rw [← splittingChartIndexAction_apply, ρ.act_eq_innerMatrix, map_mul, map_mul,
    ← map_inv m]
  rfl

/-- The relative class is independent of the chart and its matrix indices. -/
theorem relativeClass_eq_of_indices (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (f : L ⊗[K] A ≃ₐ[L] Matrix J J L) : relativeClass e = relativeClass f := by
  have h := (e.symm.trans f).toLinearEquiv.finrank_eq
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one] at h
  let r : I ≃ J := Fintype.equivOfCardEq (Nat.mul_self_inj.mp h)
  rw [← relativeClass_reindex e r]
  exact relativeClass_eq _ f

/-- Transport of the original algebra by an actual ground-field equivalence
preserves the relative class. -/
theorem relativeClass_congr (f : A ≃ₐ[K] B) (e : L ⊗[K] B ≃ₐ[L] Matrix I I L) :
    relativeClass ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) f).trans e) =
      relativeClass e := by
  let C := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) f
  let ρ := splittingChartIndexAction e
  apply descentClass_eq_of_lifts _ ρ.innerMatrix ρ.scalarDefect _ ρ.innerMatrix_mul
  intro s X
  obtain ⟨Y, rfl⟩ := (C.trans e).surjective X
  rw [← ρ.act_eq_innerMatrix, splittingChartIndexAction_apply]
  change e (C (tensorCoefficientMap s Y)) = ρ.act s (e (C Y))
  rw [splittingChartIndexAction_apply]
  congr 1
  induction Y with
  | tmul l a => simp [C, Algebra.TensorProduct.congr_apply, tensorCoefficientMap_tmul]
  | add Y Z hY hZ => simp only [map_add, hY, hZ]

/-- A chart on a split algebra gives the zero relative Brauer class. -/
theorem relativeClass_eq_zero_of_split (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (f : A ≃ₐ[K] Matrix I I K) : relativeClass e = 0 :=
  (unitClass_eq_zero_iff _ _).2 (splittingChartIndex_scalarDefect_isCoboundary_of_split e f)

/-- A zero relative Brauer class gives an actual splitting over the ground field. -/
theorem split_of_relativeClass_eq_zero [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K A] {n : ℕ} [Nonempty (Fin n)]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) (h : relativeClass e = 0) :
    Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  apply split_of_splittingChart_scalarDefect_isCoboundary e
  rw [← splittingChartIndexAction_fin_eq]
  exact (unitClass_eq_zero_iff _ _).1 h

/-- The Kronecker product of lifts multiplies their scalar factors, so the
tensor chart gives the sum of the two relative classes. -/
theorem relativeClass_tensor (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (f : L ⊗[K] B ≃ₐ[L] Matrix J J L) :
    relativeClass (tensorSplittingChart e f) = relativeClass e + relativeClass f := by
  let ρ := splittingChartIndexAction e
  let τ := splittingChartIndexAction f
  rw [relativeClass, descentClass_eq_of_lifts _
    (fun s => (ρ.innerMatrix s).kronecker (τ.innerMatrix s))
    (fun s t => ρ.scalarDefect s t * τ.scalarDefect s t)
    (tensorSplittingChart_act_eq_kronecker e f _ _ ρ.act_eq_innerMatrix τ.act_eq_innerMatrix)
    (kronecker_lifts_mul _ _ _ _ ρ.innerMatrix_mul τ.innerMatrix_mul)]
  exact unitClass_mul ρ.scalarDefect_isTwoCocycle τ.scalarDefect_isTwoCocycle _

/-- A splitting chart on the actual algebra of matrices over a split form. -/
def matrixStabilizedChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (n : ℕ) :
    L ⊗[K] Matrix (Fin n) (Fin n) A ≃ₐ[L] Matrix (I × Fin n) (I × Fin n) L :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (matrixEquivTensor (Fin n) K A)).trans
    (tensorSplittingChart e (splitPresentationChart (L := L)
      (AlgEquiv.refl : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K)))

/-- Matrix stabilization leaves the relative class unchanged. -/
theorem relativeClass_matrixStabilized (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (n : ℕ) [Nonempty (Fin n)] : relativeClass (matrixStabilizedChart e n) = relativeClass e := by
  let f : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K := AlgEquiv.refl
  rw [matrixStabilizedChart, relativeClass_congr, relativeClass_tensor,
    relativeClass_eq_zero_of_split (splitPresentationChart (L := L) f) f, add_zero]

/-- Over a common splitting extension the relative class factors through
Mathlib's actual matrix-stable equivalence. -/
theorem relativeClass_eq_of_brauerEquivalent {A B : CSA.{u, u} K}
    (h : IsBrauerEquivalent A B) (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (f : L ⊗[K] B ≃ₐ[L] Matrix J J L) : relativeClass e = relativeClass f := by
  obtain ⟨n, m, hn, hm, ⟨g⟩⟩ := h
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hm)
  rw [← relativeClass_matrixStabilized e n, ← relativeClass_matrixStabilized f m]
  refine (relativeClass_eq_of_indices _
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) g).trans
      (matrixStabilizedChart f m))).trans ?_
  exact relativeClass_congr g _

end Langlands.BrauerComparison
