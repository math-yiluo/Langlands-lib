import Langlands.GroupScheme.Quaternionic.NormOneIsometryConnectedness
import Langlands.GroupScheme.Quaternionic.NormOneIsometryAffinePoints
import Langlands.GroupScheme.OrthogonalMatrix.ScalarPoints
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Lie.BaseChange

/-! # Affine points under the split comparison of a quaternionic norm-one group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FirstKindInvolution

section Scalar

variable {K : Type u} [Field K] {m : ℕ} [NeZero m] (q : (scalar K).QuadraticForms (Fin m))
  (A : CommAlgCat.{u} (CommRingCat.of K))

variable {R : CommRingCat.{u}} in
/-- The global sections of an affine test, identified with its coefficient algebra. -/
def affineSectionsRingHom (A : CommAlgCat.{u} R) :
    Γ(((algSpec R).obj (op A)).left, ⊤) →+* A :=
  (Corepresented.affineSectionsIso A).hom.hom.toRingHom

/-- On an affine test, the test-scheme matrix of a scalar norm-one point is its affine matrix
read through the global-sections comparison. -/
theorem scalarMatrixPoint_normOne (w : ((scalar K).normOneIsometryGroup q).affinePoints A) :
    (OrthogonalMatrix.scalarMatrixPoint q A
        (w ≫ ((scalar K).normOneIsometryGroupι q).hom.hom) : Matrix (Fin m) (Fin m) A) =
      (ScalarNormOnePoints.matrix q _ w : Matrix (Fin m) (Fin m) _).map
        (affineSectionsRingHom A) := by
  set T := (algSpec (CommRingCat.of K)).obj (op A)
  set U := FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix (Fin m) (Fin m) K)) A
    (w ≫ ((scalar K).normOneIsometryAmbientι q).hom.hom) with hU
  have hL : (OrthogonalMatrix.scalarMatrixPoint q A
      (w ≫ ((scalar K).normOneIsometryGroupι q).hom.hom) : Matrix (Fin m) (Fin m) A) =
        OrthogonalMatrix.chart K (Fin m) A (U : A ⊗[K] Matrix (Fin m) (Fin m) K) := by
    change OrthogonalMatrix.chart K (Fin m) A
      ((OrthogonalMorita.isometryAffineUnitsEquiv (scalar K) q A
        (w ≫ ((scalar K).normOneIsometryGroupι q).hom.hom) :
          (A ⊗[K] Matrix (Fin m) (Fin m) K)ˣ) : A ⊗[K] Matrix (Fin m) (Fin m) K) = _
    rw [OrthogonalMorita.coe_isometryAffineUnitsEquiv]
    rfl
  have hP : FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix (Fin m) (Fin m) K)) T
      (w ≫ ((scalar K).normOneIsometryAmbientι q).hom.hom) =
      Units.map (Algebra.TensorProduct.map (Corepresented.affineSectionsIso A).inv.hom
        (AlgHom.id K (Matrix (Fin m) (Fin m) K))).toMonoidHom U :=
    Corepresented.pointsEquiv_eq_affinePointsEquiv _ _ A _
  rw [hL, ScalarNormOnePoints.matrix_apply]
  change _ = (ScalarMatrixCoordinates.matrixEquiv K ((algΓ (CommRingCat.of K)).obj T).unop
    ((FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix (Fin m) (Fin m) K)) T
      (w ≫ ((scalar K).normOneIsometryAmbientι q).hom.hom) :
        (((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix (Fin m) (Fin m) K)ˣ) :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix (Fin m) (Fin m) K)).map
            (affineSectionsRingHom A)
  rw [hP, Units.coe_map]
  have hnat := ScalarMatrixCoordinates.matrixEquiv_naturality K
    (Corepresented.affineSectionsIso A).inv.hom (U : A ⊗[K] Matrix (Fin m) (Fin m) K)
  ext i j
  rw [Matrix.map_apply]
  erw [AlgHom.coe_toRingHom, hnat]
  rw [Matrix.map_apply]
  change _ = ((Corepresented.affineSectionsIso A).inv ≫ (Corepresented.affineSectionsIso A).hom).hom _
  rw [Iso.inv_hom_id]
  rfl

end Scalar

section Quaternionic

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

open MoritaIsometry

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D] {L : Type u} [Field L] [Algebra F L]
  (e : L ⊗[F] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution F D)
  {m : ℕ} [NeZero m] (q : σ.QuadraticForms (Fin m))
  (hσ : Module.finrank F σ.symmetricSubspace = 3)

local notation "SU" => σ.normOneIsometryGroup q
local notation "Lₐ" => (CommAlgCat.of L L : CommAlgCat (CommRingCat.of L))

set_option maxHeartbeats 400000 in
/-- The split matrix of an `L`-point of the norm-one group whose tensor unit is a constant
`1 ⊗ M`, read through the split comparison, is the chart of `1 ⊗ M`. -/
theorem scalarMatrixPoint_splitIso (z : (σ.normOneIsometryGroup q).affinePoints (CommAlgCat.of F L))
    (M : Matrix (Fin m) (Fin m) D)
    (hz : ((σ.normOneIsometryAffinePointsEquiv q (CommAlgCat.of F L) z).val.val :
      L ⊗[F] Matrix (Fin m) (Fin m) D) = (1 : L) ⊗ₜ[F] M) :
    (OrthogonalMatrix.scalarMatrixPoint (NormOneSplit.gramQ e σ q) Lₐ
        (((Lie.affineBaseChangeEquiv F L SU L).symm z ≫
          (NormOneSplit.splitIso e σ q hσ).hom.hom.hom) ≫
            ((scalar L).normOneIsometryGroupι (NormOneSplit.gramQ e σ q)).hom.hom) :
          Matrix (Fin (2 * m)) (Fin (2 * m)) L) =
      chartN e m L ((1 : L) ⊗ₜ[F] M) := by
  set z' := (Lie.affineBaseChangeEquiv F L (σ.normOneIsometryGroup q) L).symm z with hz'
  set T := (algSpec (CommRingCat.of L)).obj (op Lₐ) with hT
  have h1 : z' ≫ (NormOneSplit.splitIso e σ q hσ).hom.hom.hom =
      NormOneSplit.splitPointsEquiv e σ q hσ T z' := comp_isoOfPoints_hom _ _ T z'
  have hb : GroupScheme.baseChangePointsEquiv (scalarBaseMap F L) (σ.normOneIsometryGroup q) T z' =
      (Lie.affineBaseTestIso F L L).hom ≫ z := by
    have h := (Lie.affineBaseChangeEquiv F L (σ.normOneIsometryGroup q) L).apply_symm_apply z
    rw [← hz'] at h
    change (Lie.affineBaseTestIso F L L).inv ≫
      GroupScheme.baseChangePointsEquiv (scalarBaseMap F L) (σ.normOneIsometryGroup q) T z' = z at h
    rw [← h, Iso.hom_inv_id_assoc]
  have hu : ((NormOneSplit.unitPoint σ q T z' :
      (restrictedSections F L T ⊗[F] Matrix (Fin m) (Fin m) D)ˣ) :
        restrictedSections F L T ⊗[F] Matrix (Fin m) (Fin m) D) =
      (1 : restrictedSections F L T) ⊗ₜ[F] M := by
    have key : ∀ {S S' : CommAlgCat.{u} (CommRingCat.of F)} (g : S ⟶ S')
        (v : (S ⊗[F] Matrix (Fin m) (Fin m) D)ˣ), (v : S ⊗[F] Matrix (Fin m) (Fin m) D) =
          (1 : S) ⊗ₜ[F] M →
        ((Units.map (Algebra.TensorProduct.map g.hom
          (AlgHom.id F (Matrix (Fin m) (Fin m) D))).toMonoidHom v :
            (S' ⊗[F] Matrix (Fin m) (Fin m) D)ˣ) : S' ⊗[F] Matrix (Fin m) (Fin m) D) =
              (1 : S') ⊗ₜ[F] M := by
      intro S S' g v hv
      rw [Units.coe_map]
      change Algebra.TensorProduct.map g.hom (AlgHom.id F (Matrix (Fin m) (Fin m) D))
        (v : S ⊗[F] Matrix (Fin m) (Fin m) D) = _
      rw [hv, Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.id_apply]
    have hz2 : ((FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F (Matrix (Fin m) (Fin m) D))
        (CommAlgCat.of F L) (z ≫ (σ.normOneIsometryAmbientι q).hom.hom) :
          (L ⊗[F] Matrix (Fin m) (Fin m) D)ˣ) : L ⊗[F] Matrix (Fin m) (Fin m) D) =
            (1 : L) ⊗ₜ[F] M := by
      rw [← σ.normOneIsometryAffinePointsEquiv_val]
      exact hz
    rw [NormOneSplit.unitPoint_apply, hb, Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
    erw [Corepresented.pointsEquiv_eq_affinePointsEquiv]
    exact key _ _ (key _ _ hz2)
  rw [scalarMatrixPoint_normOne (NormOneSplit.gramQ e σ q) Lₐ _, h1,
    NormOneSplit.matrix_splitPointsEquiv, NormOneSplit.matrixPoint_val, hu, chartN_one_tmul]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply]
  exact (Corepresented.affineSectionsIso _).hom.hom.commutes _

end Quaternionic

end Langlands.GroupScheme.Quaternionic
