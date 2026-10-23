import Langlands.Shimura.Unitary.ComplexKottwitzMatrices
import Langlands.Shimura.Unitary.RealReflex

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module Matrix
open scoped CategoryTheory.MonObj Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable {S : Type*} [CommRing S] [Algebra ℂ S] {n : ℕ}

/-- The common inverse-scalar weight space of a matrix family on scalar units. -/
def inverseWeightSpace (a : Sˣ → Matrix (Fin n) (Fin n) S) :
    Submodule S (Fin n → S) where
  carrier := {v | ∀ u : Sˣ, a u *ᵥ v = (↑(u⁻¹) : S) • v}
  add_mem' hv hw u := by rw [Matrix.mulVec_add, hv u, hw u, smul_add]
  zero_mem' u := by rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' c v hv u := by rw [Matrix.mulVec_smul, hv u, smul_comm]

/-- A diagonal family with inverse and trivial weights has precisely its supported coordinates. -/
theorem inverseWeightSpace_diagonal (p : Fin n → Prop) [DecidablePred p] :
    inverseWeightSpace (fun u : Sˣ => Matrix.diagonal
      (fun j : Fin n => if p j then (↑(u⁻¹) : S) else 1)) =
      ⨅ j ∈ {j | ¬ p j}, LinearMap.ker (LinearMap.proj j : (Fin n → S) →ₗ[S] S) := by
  ext v
  simp only [inverseWeightSpace, Submodule.mem_mk, Set.mem_ofPred_eq,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · intro hv j hj
    have h := congrFun (hv (-1)) j
    simp only [Matrix.mulVec_diagonal, hj, ite_false, one_mul, Pi.smul_apply,
      smul_eq_mul, inv_neg, inv_one, Units.val_neg, Units.val_one, neg_one_mul] at h
    have h2 : (2 : ℂ) • v j = 0 := by
      rw [two_smul]
      linear_combination h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  · intro hv u
    funext j
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hj : p j
    · simp [hj]
    · simp [hj, hv j hj]

/-- The rank of a diagonal inverse-weight space is the number of inverse-weight coordinates. -/
theorem finrank_inverseWeightSpace_diagonal [Nontrivial S]
    (p : Fin n → Prop) [DecidablePred p] :
    Module.finrank S (inverseWeightSpace (fun u : Sˣ => Matrix.diagonal
      (fun j : Fin n => if p j then (↑(u⁻¹) : S) else 1))) =
      (Finset.univ.filter p).card := by
  have hd : Disjoint {j | p j} {j | ¬ p j} := Set.disjoint_left.mpr fun _ hj hj' => hj' hj
  have hu : Set.univ ⊆ {j | p j} ∪ {j | ¬ p j} := fun j _ => em (p j)
  rw [inverseWeightSpace_diagonal,
    (LinearMap.iInfKerProjEquiv S (fun _ : Fin n => S) hd hu).finrank_eq,
    Module.finrank_fintype_fun_eq_card, ← Fintype.card_subtype]
  rfl

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The inverse-weight space of the actual first-factor Kottwitz cocharacter.
The Boolean selects the matrix at the chosen CM embedding or its conjugate. -/
def kottwitzMatrixWeightSpace (T : Over (Spec (CommRingCat.of ℂ)))
    (τ : E →+* ℝ) (selected : Bool) :
    Submodule (AlgebraInvolution.complexTestAlgebra T)
      (Fin n → AlgebraInvolution.complexTestAlgebra T) :=
  ComplexMatrix.inverseWeightSpace fun u =>
    let m := D.complexPointMatrices C T
      ((GroupScheme.Gm.pointsEquiv _ T).symm u ≫
        (D.kottwitzCocharacter C true).hom.hom) τ
    if selected then m.1 else m.2

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the actual cocharacter at the point corresponding to a scalar unit. -/
theorem kottwitzCocharacter_unit_matrices (T : Over (Spec (CommRingCat.of ℂ)))
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) (τ : E →+* ℝ) :
    D.complexPointMatrices C T
      ((GroupScheme.Gm.pointsEquiv _ T).symm u ≫
        (D.kottwitzCocharacter C true).hom.hom) τ =
      ComplexMatrix.splitDiagonal (AlgebraInvolution.complexTestAlgebra T) n
        (if τ = C.distinguished then n - 1 else n) (1, ↑(u⁻¹)) := by
  rw [D.kottwitzCocharacter_matrices]
  simp only [↓reduceIte, MulEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- In each split factor the actual weight space is a diagonal inverse-weight space. -/
theorem kottwitzMatrixWeightSpace_diagonal (T : Over (Spec (CommRingCat.of ℂ)))
    (τ : E →+* ℝ) (selected : Bool) :
    D.kottwitzMatrixWeightSpace C T τ selected =
      ComplexMatrix.inverseWeightSpace (fun u : (AlgebraInvolution.complexTestAlgebra T)ˣ =>
        Matrix.diagonal (fun j : Fin n =>
          if (if selected then j.val < (if τ = C.distinguished then n - 1 else n)
            else ¬ j.val < (if τ = C.distinguished then n - 1 else n))
          then (↑(u⁻¹) : AlgebraInvolution.complexTestAlgebra T) else 1)) := by
  unfold kottwitzMatrixWeightSpace
  congr 1
  funext u
  rw [D.kottwitzCocharacter_unit_matrices]
  cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    ComplexMatrix.splitDiagonal, ite_not]

/-- The matrix-weight space is exactly the coordinate submodule of its inverse weights. -/
theorem kottwitzMatrixWeightSpace_eq (T : Over (Spec (CommRingCat.of ℂ)))
    (τ : E →+* ℝ) (selected : Bool) :
    D.kottwitzMatrixWeightSpace C T τ selected =
      ⨅ j ∈ {j : Fin n | ¬ (if selected then
          j.val < (if τ = C.distinguished then n - 1 else n)
        else ¬ j.val < (if τ = C.distinguished then n - 1 else n))},
        LinearMap.ker (LinearMap.proj j :
          (Fin n → AlgebraInvolution.complexTestAlgebra T) →ₗ[
            AlgebraInvolution.complexTestAlgebra T] AlgebraInvolution.complexTestAlgebra T) := by
  rw [D.kottwitzMatrixWeightSpace_diagonal, ComplexMatrix.inverseWeightSpace_diagonal]

/-- The selected factor has inverse-weight rank equal to the positive signature. -/
theorem finrank_kottwitzMatrixWeightSpace_true (T : Over (Spec (CommRingCat.of ℂ)))
    [Nontrivial Γ(T.left, ⊤)] (τ : E →+* ℝ) :
    Module.finrank (AlgebraInvolution.complexTestAlgebra T)
      (D.kottwitzMatrixWeightSpace C T τ true) =
        if τ = C.distinguished then n - 1 else n := by
  let : Nontrivial (AlgebraInvolution.complexTestAlgebra T) := ‹Nontrivial Γ(T.left, ⊤)›
  rw [D.kottwitzMatrixWeightSpace_diagonal, ComplexMatrix.finrank_inverseWeightSpace_diagonal]
  simp only [↓reduceIte, Fin.card_filter_val_lt]
  exact min_eq_right (by split_ifs <;> omega)

/-- The conjugate factor has the complementary inverse-weight rank. -/
theorem finrank_kottwitzMatrixWeightSpace_false (T : Over (Spec (CommRingCat.of ℂ)))
    [Nontrivial Γ(T.left, ⊤)] (τ : E →+* ℝ) :
    Module.finrank (AlgebraInvolution.complexTestAlgebra T)
      (D.kottwitzMatrixWeightSpace C T τ false) =
        if τ = C.distinguished then 1 else 0 := by
  let : Nontrivial (AlgebraInvolution.complexTestAlgebra T) := ‹Nontrivial Γ(T.left, ⊤)›
  rw [D.kottwitzMatrixWeightSpace_diagonal, ComplexMatrix.finrank_inverseWeightSpace_diagonal]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    Fin.card_filter_val_lt, min_eq_right (by split_ifs <;> omega),
    Finset.card_univ, Fintype.card_fin]
  have hn := C.rank_gt_one
  split_ifs <;> omega

/-- The inverse-weight space indexed by a complex embedding of the CM field. -/
def kottwitzWeightSpace (T : Over (Spec (CommRingCat.of ℂ))) (i : K →+* ℂ) :
    Submodule (AlgebraInvolution.complexTestAlgebra T)
      (Fin n → AlgebraInvolution.complexTestAlgebra T) :=
  D.kottwitzMatrixWeightSpace C T (realPlaceBelow E i)
    (decide (i = Φ (realPlaceBelow E i)))

/-- The actual complex inverse-weight rank recovers the actual real Hodge function. -/
theorem finrank_kottwitzWeightSpace (T : Over (Spec (CommRingCat.of ℂ)))
    [Nontrivial Γ(T.left, ⊤)] (i : K →+* ℂ) :
    Module.finrank (AlgebraInvolution.complexTestAlgebra T)
      (D.kottwitzWeightSpace C T i) = D.realHodgeFunction C i := by
  rw [D.realHodgeFunction_eq, C.hodgeFunction_apply, kottwitzWeightSpace]
  by_cases hi : i = Φ (realPlaceBelow E i)
  · rw [ite_eq_left hi, show decide (i = Φ (realPlaceBelow E i)) = true from by
      exact decide_eq_true hi]
    exact D.finrank_kottwitzMatrixWeightSpace_true C T _
  · rw [ite_eq_right hi, show decide (i = Φ (realPlaceBelow E i)) = false from by
      exact decide_eq_false hi]
    exact D.finrank_kottwitzMatrixWeightSpace_false C T _

end Langlands.Shimura.CentralSimpleUnitaryData
