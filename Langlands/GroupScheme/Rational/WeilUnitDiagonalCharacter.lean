import Langlands.GroupScheme.Torus.WeilRestrictionEvaluation
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.GaloisCocycleScalarExtension
import Langlands.GroupScheme.MultiplicativePointTopology

/-! # The inclusion character of the base-changed Weil multiplicative group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Scheme

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B] [Module.Projective A B]

private def diagonalCharacterPoints (T : Over (Spec B)) :
    (T ⟶ ((GroupScheme.baseChange (baseMap A B)).obj (groupScheme A B)).X) →*
      (T ⟶ (Gm (Spec B)).X) :=
  (Gm.pointsEquiv (Spec B) T).symm.toMonoidHom.comp <|
    (evaluationUnits A B T).comp
      (GroupScheme.baseChangePointsEquiv (baseMap A B) (groupScheme A B) T).toMonoidHom

private theorem diagonalCharacterPoints_naturality {T T' : Over (Spec B)} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A B)).obj (groupScheme A B)).X) :
    diagonalCharacterPoints A B T' (a ≫ x) = a ≫ diagonalCharacterPoints A B T x := by
  apply (Gm.pointsEquiv (Spec B) T').injective
  simp only [diagonalCharacterPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, GroupScheme.baseChangePointsEquiv_naturality,
    evaluationUnits_naturality, Gm.pointsEquiv_naturality]

/-- The actual character over the coefficient algebra given by evaluation at its inclusion. -/
def diagonalCharacter :
    (GroupScheme.baseChange (baseMap A B)).obj (groupScheme A B) ⟶ (Gm (Spec B)).toGrp :=
  homOfPoints (diagonalCharacterPoints A B) (diagonalCharacterPoints_naturality A B)

private theorem diagonalCharacter_points (T : Over (Spec B))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A B)).obj (groupScheme A B)).X) :
    Gm.pointsEquiv (Spec B) T (x ≫ (diagonalCharacter A B).hom.hom) =
      evaluationUnits A B T (GroupScheme.baseChangePointsEquiv (baseMap A B) (groupScheme A B) T x) := by
  rw [diagonalCharacter, comp_homOfPoints (diagonalCharacterPoints A B)
    (diagonalCharacterPoints_naturality A B) T x]
  exact (Gm.pointsEquiv (Spec B) T).apply_symm_apply _

end Scheme

section Field

variable {F B R : Type u} [Field F] [Field B] [Algebra F B] [FiniteDimensional F B]
  [Field R] [Algebra F R] [Algebra B R] [IsScalarTower F B R]

local notation "A" => CommRingCat.of F
local notation "C" => CommRingCat.of B
local notation "W" => groupScheme A B
local notation "b" => Spec.algebraMap F B

/-- On an affine field test the character multiplies the left tensor factor into the
coefficient field, using the selected algebra structure of that factor. -/
theorem diagonalCharacter_affine (x : GaloisCocycle.cover B R ⟶ ((GroupScheme.baseChange b).obj W).X) :
    Gm.affineUnitsEquiv C (CommAlgCat.of B R)
        (x ≫ (diagonalCharacter A C).hom.hom) =
      Units.map (evaluationCoefficient F B R).toMonoidHom
        (affineUnitsEquiv A B (CommAlgCat.of F R) (GaloisCocycle.scalarExtensionPointsEquiv W x)) := by
  let T := GaloisCocycle.cover B R
  let U := GaloisCocycle.cover F R
  let _ : Algebra C (restrictedSections A C T) := restrictedSectionsAlgebra A C T
  let _ : IsScalarTower A C (restrictedSections A C T) := restrictedSectionsScalarTower A C T
  let i := Langlands.AlgebraicGeometry.PointTopology.ringTestRestrictScalarsIso F B R
  let y := GroupScheme.baseChangePointsEquiv b W T x
  let γF := Corepresented.affineSectionsIso (R := A) (CommAlgCat.of F R)
  let γB := Corepresented.affineSectionsIso (R := C) (CommAlgCat.of B R)
  let j := ((algΓ A).map i.inv).unop.hom
  let ψ := γF.hom.hom.comp j
  have hψ (r : restrictedSections A C T) : ψ r = γB.hom.hom r := by
    change γF.hom.hom (i.inv.left.appTop r) = γB.hom.hom r
    rw [Langlands.AlgebraicGeometry.PointTopology.ringTestRestrictScalarsIso_inv_left,
      Scheme.Hom.id_appTop]
    exact (DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom (R := A)
      (CommAlgCat.of F R)) r).trans
      (DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom (R := C)
        (CommAlgCat.of B R)) r).symm
  have hu := Corepresented.map_affineSectionsIso_pointsEquiv (functor A B) (corepresentableBy A B)
    (CommAlgCat.of F R) (i.inv ≫ y)
  change Units.map (Algebra.TensorProduct.lTensor (S := B) B γF.hom.hom).toMonoidHom
    (pointsEquiv A B U (i.inv ≫ y)) =
      affineUnitsEquiv A B (CommAlgCat.of F R) (GaloisCocycle.scalarExtensionPointsEquiv W x) at hu
  rw [← hu, pointsEquiv_naturality]
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    (Gm.pointsEquiv (Spec C) T (x ≫ (diagonalCharacter A C).hom.hom)).val = _
  rw [diagonalCharacter_points]
  let z := (pointsEquiv A B _ y).val
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    (evaluationCoefficient A C (restrictedSections A C T) z) =
    evaluationCoefficient F B R (Algebra.TensorProduct.lTensor (S := B) B γF.hom.hom
      (Algebra.TensorProduct.lTensor (S := B) B j z))
  calc
    _ = γB.hom.hom (evaluationCoefficient A C (restrictedSections A C T) z) :=
      (DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom (R := C)
        (CommAlgCat.of B R)) _).symm
    _ = evaluationCoefficient F B R (Algebra.TensorProduct.lTensor (S := B) B ψ z) :=
      (evaluationCoefficient_naturality A C (restrictedSections A C T) γB.hom.hom ψ hψ z).symm
    _ = _ := congrArg (evaluationCoefficient F B R)
      (DFunLike.congr_fun (Algebra.TensorProduct.map_id_comp (S := B) γF.hom.hom j) z)

end Field

end Langlands.GroupScheme.WeilGm
