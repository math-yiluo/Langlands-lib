import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentation
import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof
import Langlands.GroupScheme.AffinePointComparison

/-! # Reconstructing the orthogonal Morita comparison on actual affine points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {m : ℕ} (q : σ.QuadraticForms (Fin m))

/-- Actual affine points, refined to units satisfying their defining equations. -/
def isometryAffineUnitsEquiv (R : CommAlgCat.{u} (CommRingCat.of K)) :
    (σ.isometryGroup q).affinePoints R ≃* σ.isometryUnits (Quotient.out q) R :=
  Corepresented.affinePointsEquiv _
    (Corepresented.cutCorepresentableBy (IsometryCut.isCutOutBy
      (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix (Fin m))) (Quotient.out q))) R

/-- Refinement retains exactly the unit read through the original closed inclusion. -/
theorem coe_isometryAffineUnitsEquiv (R : CommAlgCat.{u} (CommRingCat.of K))
    (a : (σ.isometryGroup q).affinePoints R) :
    (isometryAffineUnitsEquiv σ q R a : (R ⊗[K] Matrix (Fin m) (Fin m) D)ˣ) =
      σ.isometryAffineUnitsOver q R a := by
  exact (Corepresented.groupSchemeMap_affinePoints
    (Corepresented.cutCorepresentableBy (IsometryCut.isCutOutBy
      (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix (Fin m))) (Quotient.out q)))
    (FiniteAlgebraUnits.corepresentableBy (Module.finBasis K (Matrix (Fin m) (Fin m) D)))
    (Corepresented.cutInclusion _) a).symm

/-- Refinement commutes with every coefficient change. -/
theorem isometryAffineUnitsEquiv_naturality
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S)
    (a : (σ.isometryGroup q).affinePoints R) :
    isometryAffineUnitsEquiv σ q S ((σ.isometryGroup q).affinePointMap φ a) =
      IsometryCut.isometrySubgroupMap σ.isStable_quadraticKernel (Quotient.out q) φ.hom
        (isometryAffineUnitsEquiv σ q R a) := by
  apply Subtype.ext
  rw [coe_isometryAffineUnitsEquiv, σ.isometryAffineUnitsOver_naturality]
  change Units.map _ (σ.isometryAffineUnitsOver q R a) =
    Units.map _ (isometryAffineUnitsEquiv σ q R a).val
  rw [coe_isometryAffineUnitsEquiv]

variable (L : Type u) [Field L] [Algebra K L] (n : ℕ)

/-- The algebraic input to affine reconstruction: natural isomorphisms of the
original isometry units with split orthogonal matrices over every coefficient algebra. -/
structure UnitComparison where
  equiv : ∀ (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R],
    σ.isometryUnits (Quotient.out q) R ≃* OrthogonalMatrix.orthogonalGroup (Fin n) R
  naturality : ∀ {R S : Type u} [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] [CommRing S] [Algebra K S] [Algebra L S] [IsScalarTower K L S]
    (φ : R →ₐ[L] S) (y : σ.isometryUnits (Quotient.out q) R),
    equiv S (IsometryCut.isometrySubgroupMap σ.isStable_quadraticKernel
      (Quotient.out q) (φ.restrictScalars K) y) =
      OrthogonalMatrix.map (Fin n) φ.toRingHom (equiv R y)

namespace UnitComparison

variable {σ q L n} (c : UnitComparison σ q L n)

local instance coefficientBaseAlgebra (R : CommAlgCat.{u} (CommRingCat.of L)) :
    Algebra K R := Algebra.compHom R (algebraMap K L)

local instance coefficientScalarTower (R : CommAlgCat.{u} (CommRingCat.of L)) :
    IsScalarTower K L R := IsScalarTower.of_algebraMap_eq' rfl

/-- The original group after the actual change of base. -/
abbrev baseChanged : GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (Spec.algebraMap K L)).obj (σ.isometryGroup q)

private instance isAffine_baseChanged :
    IsAffine (baseChanged (σ := σ) (q := q) (L := L)).X.left := by
  change IsAffine (Limits.pullback (σ.isometryGroup q).X.hom (Spec.algebraMap K L))
  infer_instance

/-- The canonical point comparison through the original unit and the supplied matrix. -/
def pointEquiv (R : CommAlgCat.{u} (CommRingCat.of L)) :
    (baseChanged (σ := σ) (q := q) (L := L)).affinePoints R ≃*
      (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).affinePoints R :=
  (affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q)).symm.trans <|
    (isometryAffineUnitsEquiv σ q (CommAlgCat.of (CommRingCat.of K) R)).trans <|
      (c.equiv R).trans
        (Corepresented.affinePointsEquiv (OrthogonalMatrix.functor (Fin n) (CommRingCat.of L))
          (OrthogonalMatrix.corepresentableBy (Fin n) (CommRingCat.of L)) R).symm

/-- Reading the reconstructed point recovers the supplied orthogonal matrix. -/
theorem pointEquiv_matrix (R : CommAlgCat.{u} (CommRingCat.of L))
    (a : (baseChanged (σ := σ) (q := q) (L := L)).affinePoints R) :
    Corepresented.affinePointsEquiv _
        (OrthogonalMatrix.corepresentableBy (Fin n) (CommRingCat.of L)) R
        (c.pointEquiv R a) =
      c.equiv R (isometryAffineUnitsEquiv σ q (CommAlgCat.of (CommRingCat.of K) R)
        ((affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q)).symm a)) :=
  (Corepresented.affinePointsEquiv _
    (OrthogonalMatrix.corepresentableBy (Fin n) (CommRingCat.of L)) R).apply_symm_apply _

/-- Forgetting the change of base is natural on the actual spectrum maps. -/
theorem baseChange_symm_naturality
    {R S : CommAlgCat.{u} (CommRingCat.of L)} (φ : R ⟶ S)
    (a : (baseChanged (σ := σ) (q := q) (L := L)).affinePoints R) :
    (affinePointsBaseChangeMulEquiv K L S (σ.isometryGroup q)).symm
        ((baseChanged (σ := σ) (q := q) (L := L)).affinePointMap φ a) =
      (σ.isometryGroup q).affinePointMap
        (CommAlgCat.ofHom (φ.hom.restrictScalars K))
        ((affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q)).symm a) := by
  apply Over.OverMorphism.ext
  simp only [affinePointsBaseChangeMulEquiv_symm_left, affinePointMap_apply, Over.comp_left]
  exact Category.assoc _ _ _

/-- The reconstructed point comparison commutes with all coefficient maps. -/
theorem pointEquiv_naturality
    {R S : CommAlgCat.{u} (CommRingCat.of L)} (φ : R ⟶ S)
    (a : (baseChanged (σ := σ) (q := q) (L := L)).affinePoints R) :
    c.pointEquiv S ((baseChanged (σ := σ) (q := q) (L := L)).affinePointMap φ a) =
      (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).affinePointMap φ
        (c.pointEquiv R a) := by
  apply (Corepresented.affinePointsEquiv _
    (OrthogonalMatrix.corepresentableBy (Fin n) (CommRingCat.of L)) S).injective
  rw [show (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).affinePointMap φ
      (c.pointEquiv R a) = (algSpec (CommRingCat.of L)).map φ.op ≫ c.pointEquiv R a
    from rfl, Corepresented.affinePointsEquiv_naturality]
  rw [pointEquiv_matrix, pointEquiv_matrix]
  change c.equiv S (isometryAffineUnitsEquiv σ q (CommAlgCat.of (CommRingCat.of K) S)
      ((affinePointsBaseChangeMulEquiv K L S (σ.isometryGroup q)).symm
        ((baseChanged (σ := σ) (q := q) (L := L)).affinePointMap φ a))) =
    OrthogonalMatrix.map (Fin n) φ.hom.toRingHom
      (c.equiv R (isometryAffineUnitsEquiv σ q (CommAlgCat.of (CommRingCat.of K) R)
        ((affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q)).symm a)))
  rw [baseChange_symm_naturality, isometryAffineUnitsEquiv_naturality]
  exact c.naturality φ.hom _

/-- The natural isomorphism of actual affine group-valued points. -/
def affinePointIso :
    (baseChanged (σ := σ) (q := q) (L := L)).affinePointFunctor ≅
      (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).affinePointFunctor :=
  NatIso.ofComponents (fun R => (c.pointEquiv R).toGrpIso) (by
    intro R S φ
    ext a
    exact c.pointEquiv_naturality φ a)

/-- An actual group-scheme isomorphism reconstructed from the given unit comparisons. -/
def groupIso :
    (GroupScheme.baseChange (Spec.algebraMap K L)).obj (σ.isometryGroup q) ≅
      OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L) := by
  letI := OrthogonalMatrix.isAffine_groupScheme (Fin n) (CommRingCat.of L)
  exact AffinePointComparison.iso c.affinePointIso

/-- Reconstruction retains the original affine-point formula. -/
theorem groupIso_hom_points (R : CommAlgCat.{u} (CommRingCat.of L))
    (a : (baseChanged (σ := σ) (q := q) (L := L)).affinePoints R) :
    a ≫ c.groupIso.hom.hom.hom = c.pointEquiv R a := by
  have := OrthogonalMatrix.isAffine_groupScheme (Fin n) (CommRingCat.of L)
  exact AffinePointComparison.iso_hom_points c.affinePointIso R a

/-- The matrix formula on the canonical coefficient algebra. -/
theorem affineMatrix_splitPoint_canonical (R : CommAlgCat.{u} (CommRingCat.of L))
    (a : (σ.isometryGroup q).affinePoints (CommAlgCat.of (CommRingCat.of K) R)) :
    MatrixRepresentation.affineMatrix
        (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L)) R
        (splitPoint σ q c.groupIso R a) =
      OrthogonalMatrix.toGL (c.equiv R (isometryAffineUnitsEquiv σ q
        (CommAlgCat.of (CommRingCat.of K) R) a)) := by
  unfold splitPoint
  rw [groupIso_hom_points]
  have h := Corepresented.groupSchemeMap_affinePoints
    (OrthogonalMatrix.corepresentableBy (Fin n) (CommRingCat.of L))
    (GeneralLinear.corepresentableBy (Fin n ⊕ Fin n) (CommRingCat.of L))
    OrthogonalMatrix.toGeneralLinear
    (c.pointEquiv R (affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q) a))
  change MatrixRepresentation.affineMatrix
      (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L)) R
      (c.pointEquiv R (affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q) a)) =
    OrthogonalMatrix.toGL
      (Corepresented.affinePointsEquiv _
        (OrthogonalMatrix.corepresentableBy (Fin n) (CommRingCat.of L)) R
        (c.pointEquiv R (affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q) a))) at h
  rw [pointEquiv_matrix, MulEquiv.symm_apply_apply] at h
  exact h

attribute [-instance] coefficientBaseAlgebra coefficientScalarTower

/-- The reconstructed matrix formula over every compatible coefficient algebra. -/
theorem affineMatrix_splitPoint
    (R : Type u) [CommRing R] [aR : Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (a : (σ.isometryGroup q).affinePoints (CommAlgCat.of (CommRingCat.of K) R)) :
    MatrixRepresentation.affineMatrix
        (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
        (CommAlgCat.of (CommRingCat.of L) R)
        (splitPoint σ q c.groupIso R a) =
      OrthogonalMatrix.toGL (c.equiv R (isometryAffineUnitsEquiv σ q
        (CommAlgCat.of (CommRingCat.of K) R) a)) := by
  have h : aR = Algebra.compHom R (algebraMap K L) :=
    Algebra.algebra_ext _ _ (IsScalarTower.algebraMap_apply K L R)
  subst aR
  exact c.affineMatrix_splitPoint_canonical (CommAlgCat.of (CommRingCat.of L) R) a

end UnitComparison

end Langlands.GroupScheme.Quaternionic.OrthogonalMorita
