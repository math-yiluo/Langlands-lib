import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.Lie.AffineCoordinates

/-! # Dual fixed vectors of reductive groups over characteristic-zero fields -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The base change of a coordinate representation to an algebraic closure. -/
def algebraicClosureBaseChange (ρ : MatrixRepresentation H n) :
    MatrixRepresentation ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H) n :=
  (GroupScheme.baseChange (toAlgebraicClosure k)).map ρ ≫
    (GeneralLinear.baseChangeIso n (toAlgebraicClosure k)).hom

/-- The base-changed representation has the original matrices on every test. -/
theorem algebraicClosureBaseChange_pointMatrix (ρ : MatrixRepresentation H n)
    (T : Over (Spec (CommRingCat.of (AlgebraicClosure k))))
    (g : T ⟶ ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X) :
    ρ.algebraicClosureBaseChange.pointMatrix T g =
      ρ.pointMatrix ((Over.map (toAlgebraicClosure k)).obj T)
        (baseChangePointsEquiv (toAlgebraicClosure k) H T g) := by
  rw [pointMatrix_apply, pointMatrix_apply]
  simp only [algebraicClosureBaseChange, Grp.comp_hom_hom]
  rw [← Category.assoc, GeneralLinear.pointsEquiv_comp_baseChangeIso_hom,
    baseChangePointsEquiv_comp]

/-- Fixed vectors remain fixed after base change to an algebraic closure. -/
theorem IsFixedVector.algebraicClosureBaseChange {ρ : MatrixRepresentation H n}
    {v : n → k} (hv : ρ.IsFixedVector v) :
    ρ.algebraicClosureBaseChange.IsFixedVector
      (fun i => algebraMap k (AlgebraicClosure k) (v i)) := by
  intro T g
  rw [algebraicClosureBaseChange_pointMatrix]
  have h := hv _ (baseChangePointsEquiv (toAlgebraicClosure k) H T g)
  have e (a : k) : scalarMap ((Over.map (toAlgebraicClosure k)).obj T) a =
      scalarMap T (algebraMap k (AlgebraicClosure k) a) :=
    scalarMap_overMap_specMap _ T a
  simpa only [e] using h

/-- Inverse-transpose fixedness is transpose fixedness. -/
theorem contragredient_mulVec_eq_iff {A : Type u} [CommRing A] (g : GL n A) (w : n → A) :
    (GeneralLinear.matrixContragredient n A g : Matrix n n A) *ᵥ w = w ↔
      (g : Matrix n n A).transpose *ᵥ w = w := by
  rw [GeneralLinear.matrixContragredient_coe]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]

variable [IsAffineHom H.X.hom]

/-- A dual fixed vector over an algebraic closure descends to a dual fixed vector over the
original field with the same pairing against an original vector. -/
theorem exists_dual_fixed_of_algebraicClosure (ρ : MatrixRepresentation H n)
    (v : n → k) (cK : n → AlgebraicClosure k)
    (hcK : ρ.algebraicClosureBaseChange.dual.IsFixedVector cK)
    (hcv : cK ⬝ᵥ (fun i => algebraMap k (AlgebraicClosure k) (v i)) = 1) :
    ∃ c : n → k, ρ.dual.IsFixedVector c ∧ c ⬝ᵥ v = 1 := by
  let K := AlgebraicClosure k
  let B := Lie.coordinateAlgebra H
  let ψ := Lie.coordinateIso H
  let S := K ⊗[k] B
  let A : CommAlgCat.{u} (CommRingCat.of K) := CommAlgCat.of (CommRingCat.of K) S
  let A₀ : CommAlgCat.{u} (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) S
  let incR : B ⟶ A₀ := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let y₀ : (algSpec (CommRingCat.of k)).obj (op A₀) ⟶ H.X :=
    (algSpec (CommRingCat.of k)).map incR.op ≫ ψ.hom
  let x : (algSpec (CommRingCat.of K)).obj (op A) ⟶
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X :=
    (baseChangePointsEquiv (toAlgebraicClosure k) H _).symm
      ((CocharacterSplitting.testIso K S).hom ≫ y₀)
  let P := ρ.affineMatrix B ψ.hom
  -- The base-changed matrix at this point is the universal matrix in the second factor.
  have hq : Function.Injective (Corepresented.affineSectionsIso A).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
  have hmat : ρ.algebraicClosureBaseChange.affineMatrix A x =
      Matrix.GeneralLinearGroup.map incR.hom.toRingHom P := by
    have h1 := ρ.algebraicClosureBaseChange.pointMatrix_eq_affineMatrix A x
    rw [algebraicClosureBaseChange_pointMatrix, MulEquiv.apply_symm_apply,
      pointMatrix_naturality, pointMatrix_eq_affineMatrix, affineMatrix_naturality] at h1
    apply Units.ext
    apply Matrix.map_injective hq
    exact (congrArg Units.val h1).symm
  have hfixK := hcK.affine A x
  rw [dual_affineMatrix, contragredient_mulVec_eq_iff, hmat] at hfixK
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero (α := K))
  refine ⟨fun i => φ (cK i), ?_, ?_⟩
  · rw [isFixedVector_iff_affine_model ρ.dual ψ, dual_affineMatrix,
      contragredient_mulVec_eq_iff]
    apply fixed_tensor_coefficients (P : Matrix n n B).transpose cK _ φ
    have hT : (P : Matrix n n B).transpose.map
        (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) =
          ((Matrix.GeneralLinearGroup.map incR.hom.toRingHom P : GL n S) :
            Matrix n n S).transpose := by
      rw [Matrix.transpose_map]
      rfl
    rw [hT]
    exact hfixK
  · have h := congrArg φ hcv
    rw [hφ] at h
    rw [← h]
    simp only [dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (cK i), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- Characteristic-zero complete reducibility over an algebraic closure supplies, for a
connected reductive group over any characteristic-zero field, a fixed dual vector taking
value one at a prescribed nonzero fixed vector. -/
theorem exists_dual_fixed_of_semisimplicity
    (hss : ReductiveCharZeroSemisimplicityStatement.{u}) [CharZero k]
    (hH : IsConnectedReductive H) (ρ : MatrixRepresentation H n)
    (v : n → k) (hv : v ≠ 0) (hfix : ρ.IsFixedVector v) :
    ∃ c : n → k, ρ.dual.IsFixedVector c ∧ c ⬝ᵥ v = 1 := by
  have hHbar := hH.baseChange_toAlgebraicClosure
  have hHbarPseudo :
      IsPseudoReductive ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H) :=
    { smooth := hHbar.smooth
      isAffineHom := hHbar.isAffineHom
      connectedSpace := hHbar.connectedSpace
      hasTrivialUnipotentRadical := hH.hasTrivialGeometricUnipotentRadical }
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X.hom :=
    hHbar.smooth
  have hvK : (fun i => algebraMap k (AlgebraicClosure k) (v i)) ≠ 0 := by
    intro h
    apply hv
    funext i
    exact (algebraMap k (AlgebraicClosure k)).injective
      ((congrFun h i).trans (map_zero _).symm)
  obtain ⟨cK, hcK, hcv⟩ := exists_dual_fixed_of_rational_semisimple
    ρ.algebraicClosureBaseChange
    (hss (AlgebraicClosure k) _ hHbarPseudo n ρ.algebraicClosureBaseChange) _ hvK
    hfix.algebraicClosureBaseChange
  exact exists_dual_fixed_of_algebraicClosure ρ v cK hcK hcv

end Langlands.GroupScheme.MatrixRepresentation
