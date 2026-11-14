import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaWeightBasis

/-! # Transport of actual row eigenvectors through an orthogonal Morita comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic

namespace OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Field L] [Algebra K L] {m n degree : ℕ}

/-- Extend a tensor row by its coefficient factor. -/
def scalarRow
    (S : Type u) [CommRing S] [Algebra K S] [Algebra L S] [IsScalarTower K L S] :
    L ⊗[K] (Fin m → D) →ₗ[K] S ⊗[K] (Fin m → D) :=
  TensorProduct.map ((Algebra.ofId L S).restrictScalars K).toLinearMap LinearMap.id

theorem rowEquivOver_self
    (e : L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L)))
    (z : L ⊗[K] (Fin m → D)) :
    rowEquivOver e L z = e z := by
  induction z with
  | tmul r v =>
    funext j x
    rw [rowEquivOver_tmul]
    have hr : r ⊗ₜ[K] v = r • ((1 : L) ⊗ₜ[K] v) := by
      simp [TensorProduct.smul_tmul']
    rw [hr, _root_.map_smul]
    simp [mul_comm]
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]

/-- The canonical extended comparison maps an extended row to the coefficient
extension of its original image. -/
theorem rowEquivOver_scalarRow
    (e : L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L)))
    (S : Type u) [CommRing S] [Algebra K S] [Algebra L S] [IsScalarTower K L S]
    (z : L ⊗[K] (Fin m → D)) :
    rowEquivOver e S (scalarRow S z) =
      fun j x => algebraMap L S (e z j x) := by
  simpa only [scalarRow, rowEquivOver_self, Algebra.ofId_apply] using
    rowEquivOver_naturality e (Algebra.ofId L S) z

end OrthogonalMorita

namespace FirstKindInvolution

open OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Field L] [Algebra K L]
  (σ : FirstKindInvolution K D) {m : ℕ} (q : σ.QuadraticForms (Fin m))
  (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)

omit [FiniteDimensional K D] in
private theorem piRight_scalarRow_extended (z : L ⊗[K] (Fin m → D)) :
    TensorProduct.piRight K
        (cocharacterExtendedTestAlgebra K (CommAlgCat.of (CommRingCat.of K) L))
        (cocharacterExtendedTestAlgebra K (CommAlgCat.of (CommRingCat.of K) L))
        (fun _ : Fin m => D)
        (scalarRow
          (cocharacterExtendedTestAlgebra K (CommAlgCat.of (CommRingCat.of K) L)) z) =
      cocharacterExtendedRow (CommAlgCat.of (CommRingCat.of K) L) z := by
  induction z with
  | tmul r v => rfl
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]

/-- Eigenvector equations for the actual tensor row action over all
coefficient `L`-algebras imply membership in the actual extended weight space. -/
theorem mem_cocharacterWeightSpaceOver_of_tensor_eigen
    (z : L ⊗[K] (Fin m → D)) (c : ℤ)
    (hz : ∀ (S : Type u) [CommRing S] [Algebra K S] [Algebra L S]
        [IsScalarTower K L S]
        (t : GroupScheme.affinePoints
          (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
          (CommAlgCat.of (CommRingCat.of K) S)),
      σ.isometryTensorRowAction q (CommAlgCat.of (CommRingCat.of K) S)
          (t ≫ f.hom.hom) (scalarRow S z) =
        (((Gm.affineUnitsEquiv (CommRingCat.of K)
          (CommAlgCat.of (CommRingCat.of K) S) t) ^ c : Sˣ) : S) • scalarRow S z) :
    z ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) c := by
  let R := CommAlgCat.of (CommRingCat.of K) L
  let S := cocharacterExtendedTestAlgebra K R
  have h := hz S (cocharacterExtendedTestPoint R)
  have h' := congrArg (TensorProduct.piRight K S S (fun _ : Fin m => D)) h
  rw [σ.piRight_isometryTensorRowAction, _root_.map_smul,
    piRight_scalarRow_extended] at h'
  change σ.cocharacterWeightEquationOver q f R c z = 0
  change σ.isometryRowActionOver q S
      (cocharacterExtendedTestPoint R ≫ f.hom.hom)
      (cocharacterExtendedRow R z) - cocharacterExtendedMonomialRow R c z = 0
  rw [sub_eq_zero, cocharacterExtendedMonomialRow_eq_smul]
  rw [cocharacterExtendedTestPoint_zpow_val] at h'
  exact h'

end FirstKindInvolution

namespace OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Field L] [Algebra K L]
  {σ : FirstKindInvolution K D} {m n degree : ℕ}
  {q : σ.QuadraticForms (Fin m)}

/-- A supplied split eigenvector law transports through the actual Morita
intertwining to all-test weights of the pulled-back copy basis. -/
theorem rowBasis_mem_of_split_eigen
    (e : OrthogonalMoritaComparison σ q L degree n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    {I : Type*} (b : Basis I L ((Fin n ⊕ Fin n) → L)) (w : I → ℤ)
    (hb : ∀ (S : Type u) [CommRing S] [Algebra K S] [Algebra L S]
        [IsScalarTower K L S]
        (t : GroupScheme.affinePoints
          (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
          (CommAlgCat.of (CommRingCat.of K) S)) (i : I),
      Matrix.vecMul (fun x => algebraMap L S (b i x))
          ((MatrixRepresentation.affineMatrix
            (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
            (CommAlgCat.of (CommRingCat.of L) S)
            (splitPoint σ q e.groupIso S (t ≫ f.hom.hom)))⁻¹ :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) S) =
        (((Gm.affineUnitsEquiv (CommRingCat.of K)
          (CommAlgCat.of (CommRingCat.of K) S) t) ^ w i : Sˣ) : S) •
          (fun x => algebraMap L S (b i x))) (p : Fin degree × I) :
    rowBasis e b p ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) (w p.2) := by
  classical
  apply σ.mem_cocharacterWeightSpaceOver_of_tensor_eigen q f
  intro S _ _ _ _ t
  apply (rowEquivOver e.rowEquiv S).injective
  rw [e.intertwines, _root_.map_smul, rowEquivOver_scalarRow, rowEquiv_rowBasis]
  funext j x
  by_cases hj : j = p.1
  · subst j
    simpa only [Pi.single_eq_same, Pi.smul_apply] using congrFun (hb S t p.2) x
  · simp [Pi.single_eq_of_ne hj, Matrix.vecMul, dotProduct]

end OrthogonalMorita

end Langlands.GroupScheme.Quaternionic
