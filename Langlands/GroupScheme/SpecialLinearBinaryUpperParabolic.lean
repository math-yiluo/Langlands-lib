import Langlands.GroupScheme.SpecialLinearBaseChange
import Langlands.GroupScheme.SpecialLinearBinaryUpperBorel
import Langlands.GroupScheme.Absolute.BorelTransport

/-! # The actual binary triangular special linear parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

section BaseChange

variable {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)

/-- Pullback and new-base models have the same upper-triangular matrices on all tests. -/
def baseChangeModelPointsEquiv (T : Over (Spec R')) :
    (T ⟶ ((GroupScheme.baseChange b).obj (groupScheme R)).X) ≃*
      (T ⟶ (groupScheme R').X) :=
  ((baseChangePointsEquiv b (groupScheme R) T).trans
    (pointsEquiv R ((Over.map b).obj T))).trans (pointsEquiv R' T).symm

/-- The two point comparisons preserve the actual triangular inclusion. -/
theorem baseChangeModelPointsEquiv_inclusion (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme R)).X) :
    baseChangeModelPointsEquiv b T x ≫ (inclusion R').hom.hom =
      SpecialLinear.baseChangeModelPointsEquiv (Fin 2) b T
        (x ≫ ((GroupScheme.baseChange b).map (inclusion R)).hom.hom) := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R' T).injective
  rw [pointsEquiv_inclusion]
  simp only [baseChangeModelPointsEquiv, SpecialLinear.baseChangeModelPointsEquiv,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [baseChangePointsEquiv_comp, pointsEquiv_inclusion]

theorem baseChangeModelPointsEquiv_naturality {T T' : Over (Spec R')}
    (a : T' ⟶ T) (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme R)).X) :
    baseChangeModelPointsEquiv b T' (a ≫ x) =
      a ≫ baseChangeModelPointsEquiv b T x := by
  have : Mono (inclusion R').hom.hom := Corepresented.mono_cutHom (isCutOutBy R')
  apply (cancel_mono (inclusion R').hom.hom).mp
  simp only [Category.assoc, baseChangeModelPointsEquiv_inclusion,
    SpecialLinear.baseChangeModelPointsEquiv_naturality]

/-- The actual binary triangular group commutes with arbitrary affine base change. -/
def baseChangeModelIso :
    (GroupScheme.baseChange b).obj (groupScheme R) ≅ groupScheme R' :=
  isoOfPoints (baseChangeModelPointsEquiv b) (baseChangeModelPointsEquiv_naturality b)

/-- The model isomorphism identifies the actual base-changed inclusion with the
inclusion constructed over the new base. -/
theorem baseChangeModelIso_hom_comp :
    (baseChangeModelIso b).hom ≫ inclusion R' =
      (GroupScheme.baseChange b).map (inclusion R) ≫
        (SpecialLinear.baseChangeModelIso (Fin 2) b).hom := by
  apply hom_ext_points
  intro T x
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [baseChangeModelIso, comp_isoOfPoints_hom,
    SpecialLinear.baseChangeModelIso, comp_isoOfPoints_hom,
    baseChangeModelPointsEquiv_inclusion]

end BaseChange

section Field

variable {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

/-- The actual base change of the triangular inclusion is Borel over every field extension. -/
theorem isBorelSubgroup_baseChange_inclusion :
    IsBorelSubgroup ((GroupScheme.baseChange b).map (inclusion (CommRingCat.of k))) := by
  have h := ((isBorelSubgroup_inclusion K).iso_comp (baseChangeModelIso b)).comp_iso
    (SpecialLinear.baseChangeModelIso (Fin 2) b).symm
  change IsBorelSubgroup
    (((baseChangeModelIso b).hom ≫ inclusion (CommRingCat.of K)) ≫
      (SpecialLinear.baseChangeModelIso (Fin 2) b).inv) at h
  rwa [baseChangeModelIso_hom_comp, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] at h

variable (k) in
/-- The actual upper-triangular determinant-one inclusion is parabolic over every field. -/
theorem isParabolicSubgroup_inclusion :
    IsParabolicSubgroup (inclusion (CommRingCat.of k)) where
  isClosedSubgroup := isClosedSubgroup_inclusion _
  smooth := Coordinates.smooth_groupScheme _
  exists_isBorelSubgroup :=
    ⟨_, _, 𝟙 _, isBorelSubgroup_baseChange_inclusion (toAlgebraicClosure k),
      Category.id_comp _⟩

variable (k) in
/-- The explicit triangular inclusion packaged with its proved parabolic property. -/
def parabolicRepresentative :
    {i : groupScheme (CommRingCat.of k) ⟶ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) //
      IsParabolicSubgroup i} :=
  ⟨inclusion (CommRingCat.of k), isParabolicSubgroup_inclusion k⟩

end Field

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
