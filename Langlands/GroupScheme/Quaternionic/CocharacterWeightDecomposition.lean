import Langlands.GroupScheme.Quaternionic.CocharacterWeightProjectors
import Langlands.GroupScheme.Quaternionic.IsometryTorusWeights
import Mathlib.Algebra.DirectSum.Module

/-! # Decomposition into all-test cocharacter row weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped Matrix TensorProduct DirectSum CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

/-- A regular coefficient eigenvector gives its eigenvalue on every row over
every coefficient algebra. -/
theorem isometryRowActionOver_of_regular_eigenvector (q : σ.QuadraticForms n)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (a : (σ.isometryGroup q).affinePoints R) (M : Matrix n n D) (c : R)
    (h : ((σ.isometryRegularRepresentation q).affineMatrix R a :
        Matrix _ _ R) *ᵥ
          (fun j => algebraMap K R ((finBasis K (Matrix n n D)).equivFun M j)) =
        c • (fun j => algebraMap K R ((finBasis K (Matrix n n D)).equivFun M j)))
    (r : n) :
    σ.isometryRowActionOver q R a (fun j => (1 : R) ⊗ₜ[K] M r j) =
      fun j => c ⊗ₜ[K] M r j := by
  let b := finBasis K (Matrix n n D)
  let x : R ⊗[K] Matrix n n D := 1 ⊗ₜ[K] M
  let z : R ⊗[K] Matrix n n D :=
    ((σ.isometryAffineUnitsOver q R a)⁻¹ : (R ⊗[K] Matrix n n D)ˣ)
  have hmat : ((σ.isometryRegularRepresentation q).affineMatrix R a :
      Matrix _ _ R) =
      LinearMap.toMatrix (b.baseChange R) (b.baseChange R) (LinearMap.mulRight R z) := by
    change ((FiniteAlgebraUnits.rightRegularHom b).affineMatrix R
      (a ≫ (σ.isometryGroupι q).hom.hom) :
        Matrix (Fin (finrank K (Matrix n n D))) (Fin (finrank K (Matrix n n D))) R) = _
    rw [FiniteAlgebraUnits.rightRegularHom_affineMatrix]
    rfl
  have hx : (b.baseChange R).equivFun x =
      fun j => algebraMap K R (b.equivFun M j) := by
    funext j
    simp [x, Basis.equivFun_apply, Algebra.smul_def]
  have hmul : x * z = c ⊗ₜ[K] M := by
    apply (b.baseChange R).equivFun.injective
    have he := LinearMap.toMatrix_mulVec_repr (b.baseChange R) (b.baseChange R)
      (LinearMap.mulRight R z) x
    change _ *ᵥ (b.baseChange R).equivFun x =
      (b.baseChange R).equivFun (x * z) at he
    rw [hx, ← hmat, h] at he
    rw [← he]
    funext j
    simp [b, Basis.equivFun_apply, Algebra.smul_def, mul_comm]
  have he := congrArg (TensorMatrix.equiv R n) hmul
  rw [_root_.map_mul, TensorMatrix.equiv_tmul, TensorMatrix.equiv_tmul] at he
  funext j
  exact congrFun (congrFun he r) j

/-- The coefficient matrix of a cocharacter in its inverse-right regular representation. -/
def cocharacterCoefficientMatrix (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (m : PUnit.{u + 1} → ℤ) (j : Fin (finrank K (Matrix n n D))) : Matrix n n D :=
  (finBasis K (Matrix n n D)).equivFun.symm
    (GeneralLinear.CocharacterDiagonal.coefficientColumn PUnit
      ((splitTorus.gmIso (Spec (CommRingCat.of K))).inv ≫
        f ≫ σ.isometryRegularRepresentation q) m j)

/-- Each row of a universal coefficient matrix has its actual integer cocharacter weight. -/
theorem cocharacterCoefficientMatrix_row_mem (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (m : PUnit.{u + 1} → ℤ) (j : Fin (finrank K (Matrix n n D))) (r : n) :
    σ.cocharacterCoefficientMatrix q f m j r ∈ σ.cocharacterWeightSpace q f (m PUnit.unit) := by
  let ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of K)) PUnit)
      (Fin (finrank K (Matrix n n D))) :=
    (splitTorus.gmIso (Spec (CommRingCat.of K))).inv ≫
      f ≫ σ.isometryRegularRepresentation q
  let R := cocharacterWeightTestAlgebra K
  let x := cocharacterWeightUniversalPoint K
  let t := splitTorus.algebraPointsEquiv PUnit (LaurentPolynomial K)
    (x ≫ (splitTorus.gmIso (Spec (CommRingCat.of K))).hom.hom.hom)
  have hρ : (splitTorus.gmIso (Spec (CommRingCat.of K))).hom ≫ ρ =
      f ≫ σ.isometryRegularRepresentation q := by
    dsimp only [ρ]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hm : GeneralLinear.CocharacterDiagonal.matrixAt PUnit ρ t =
      (σ.isometryRegularRepresentation q).affineMatrix R (x ≫ f.hom.hom) := by
    dsimp only [GeneralLinear.CocharacterDiagonal.matrixAt, t]
    rw [MulEquiv.symm_apply_apply, MatrixRepresentation.affineMatrix_apply, Category.assoc]
    change GeneralLinear.affinePointsEquiv _ _ R
      (x ≫ ((splitTorus.gmIso (Spec (CommRingCat.of K))).hom ≫ ρ).hom.hom) = _
    rw [hρ]
    rfl
  have ht : t = fun _ => Gm.relativeCoordUnit K := by
    have h := GeneralLinear.CocharacterDiagonal.algebraPointsEquiv_comp_gmIso x
    exact h.trans (congrArg (fun z => fun _ : PUnit => z)
      (cocharacterWeightUniversalPoint_unit K))
  have he := GeneralLinear.CocharacterDiagonal.coefficientColumn_weight PUnit ρ t m j
  rw [hm, ht] at he
  have hvalue : (splitTorus.exponentValue PUnit (fun _ => Gm.relativeCoordUnit K)
      (Multiplicative.ofAdd m) : LaurentPolynomial K) =
      LaurentPolynomial.T (m PUnit.unit) := by
    simpa [splitTorus.exponentValue, MonoidHom.pi] using
      Gm.relativeCoordUnit_zpow_val K (m PUnit.unit)
  rw [hvalue] at he
  apply (σ.mem_cocharacterWeightSpace_iff_universal q f (m PUnit.unit) _).mpr
  apply σ.isometryRowActionOver_of_regular_eigenvector q R (x ≫ f.hom.hom)
    (σ.cocharacterCoefficientMatrix q f m j) (LaurentPolynomial.T (m PUnit.unit)) _ r
  simpa only [cocharacterCoefficientMatrix, LinearEquiv.apply_symm_apply] using he

/-- The all-test cocharacter weight spaces span the entire division-algebra row module. -/
theorem iSup_cocharacterWeightSpace_eq_top (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    (⨆ c : ℤ, σ.cocharacterWeightSpace q f c) = ⊤ := by
  classical
  apply top_unique
  intro v _
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv]
    exact Submodule.zero_mem _
  | inr hn =>
    let r : n := Classical.choice hn
    let ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of K)) PUnit)
        (Fin (finrank K (Matrix n n D))) :=
      (splitTorus.gmIso (Spec (CommRingCat.of K))).inv ≫
        f ≫ σ.isometryRegularRepresentation q
    obtain ⟨b, w, hw⟩ := GeneralLinear.CocharacterDiagonal.exists_coefficientBasis PUnit ρ
    let B := b.map (finBasis K (Matrix n n D)).equivFun.symm
    let S := ⨆ c : ℤ, σ.cocharacterWeightSpace q f c
    have hB (j : Fin (finrank K (Matrix n n D))) : B j r ∈ S := by
      have he : B j = σ.cocharacterCoefficientMatrix q f (w j).1 (w j).2 := by
        change (finBasis K (Matrix n n D)).equivFun.symm (b j) = _
        rw [hw j]
        rfl
      rw [he]
      exact Submodule.mem_iSup_of_mem ((w j).1 PUnit.unit)
        (σ.cocharacterCoefficientMatrix_row_mem q f _ _ r)
    let M : Matrix n n D := fun _ => v
    have he : (∑ j, B.repr M j • B j r) = v := by
      funext l
      simpa only [Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply] using
        congrArg (fun A : Matrix n n D => A r l) (B.sum_repr M)
    rw [← he]
    exact Submodule.sum_mem S (fun j _ => (S.restrictScalars K).smul_mem _ (hB j))

/-- The all-test cocharacter row spaces form an internal direct sum over `D`. -/
theorem cocharacterWeightSpace_isInternal (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    DirectSum.IsInternal (σ.cocharacterWeightSpace q f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (σ.cocharacterWeightSpace_iSupIndep q f) (σ.iSup_cocharacterWeightSpace_eq_top q f)

/-- The canonical decomposition of a row into its integer cocharacter weight components. -/
def cocharacterWeightDecomposition (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    (n → D) ≃ₗ[D] ⨁ c : ℤ, σ.cocharacterWeightSpace q f c :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (σ.cocharacterWeightSpace q f))
    (σ.cocharacterWeightSpace_isInternal q f)).symm

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
