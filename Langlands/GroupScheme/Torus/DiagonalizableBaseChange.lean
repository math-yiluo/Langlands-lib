import Langlands.GroupScheme.Torus.KernelDiagonalizable

/-! # Base change of diagonalizable group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

variable {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
  (Λ : Type u) [AddCommGroup Λ]

/-- Base-changed diagonalizable points are characters with values in global units. -/
def baseChangeCharacterPointsEquiv (U : Over (Spec R')) :
    (U ⟶ ((GroupScheme.baseChange b).obj (groupScheme R Λ).toGrp).X) ≃*
      (Multiplicative Λ →* (Γ(U.left, ⊤))ˣ) :=
  (baseChangePointsEquiv b (groupScheme R Λ).toGrp U).trans
    (characterPointsEquiv R Λ ((Over.map b).obj U))

theorem baseChangeCharacterPointsEquiv_naturality
    {U U' : Over (Spec R')} (f : U' ⟶ U)
    (x : U ⟶ ((GroupScheme.baseChange b).obj (groupScheme R Λ).toGrp).X)
    (m : Λ) :
    baseChangeCharacterPointsEquiv b Λ U' (f ≫ x) (.ofAdd m) =
      Units.map f.left.appTop.hom.toMonoidHom
        (baseChangeCharacterPointsEquiv b Λ U x (.ofAdd m)) := by
  unfold baseChangeCharacterPointsEquiv
  rw [MulEquiv.trans_apply, baseChangePointsEquiv_naturality,
    characterPointsEquiv_naturality]
  rfl

theorem baseChangeIso_naturality
    {U U' : Over (Spec R')} (f : U' ⟶ U)
    (x : U ⟶ ((GroupScheme.baseChange b).obj (groupScheme R Λ).toGrp).X) :
    (characterPointsEquiv R' Λ U').symm
        (baseChangeCharacterPointsEquiv b Λ U' (f ≫ x)) =
      f ≫ (characterPointsEquiv R' Λ U).symm
        (baseChangeCharacterPointsEquiv b Λ U x) := by
  apply (characterPointsEquiv R' Λ U').injective
  apply MonoidHom.ext
  intro m
  change characterPointsEquiv R' Λ U'
      ((characterPointsEquiv R' Λ U').symm
        (baseChangeCharacterPointsEquiv b Λ U' (f ≫ x))) (.ofAdd m.toAdd) =
    characterPointsEquiv R' Λ U'
      (f ≫ (characterPointsEquiv R' Λ U).symm
        (baseChangeCharacterPointsEquiv b Λ U x)) (.ofAdd m.toAdd)
  rw [MulEquiv.apply_symm_apply, characterPointsEquiv_naturality,
    MulEquiv.apply_symm_apply, baseChangeCharacterPointsEquiv_naturality]

/-- The canonical comparison for diagonalizable groups, valid on every test scheme. -/
def baseChangeIso :
    (GroupScheme.baseChange b).obj (groupScheme R Λ).toGrp ≅
      (groupScheme R' Λ).toGrp :=
  isoOfPoints
    (fun U => (baseChangeCharacterPointsEquiv b Λ U).trans
      (characterPointsEquiv R' Λ U).symm)
    (baseChangeIso_naturality b Λ)

/-- The comparison preserves the full character-valued point. -/
@[simp]
theorem characterPointsEquiv_baseChangeIso_hom (U : Over (Spec R'))
    (x : U ⟶ ((GroupScheme.baseChange b).obj (groupScheme R Λ).toGrp).X) :
    characterPointsEquiv R' Λ U (x ≫ (baseChangeIso b Λ).hom.hom.hom) =
      baseChangeCharacterPointsEquiv b Λ U x := by
  have h := comp_isoOfPoints_hom
    (fun U => (baseChangeCharacterPointsEquiv b Λ U).trans
      (characterPointsEquiv R' Λ U).symm)
    (baseChangeIso_naturality b Λ) U x
  rw [show x ≫ (baseChangeIso b Λ).hom.hom.hom = _ from h]
  exact MulEquiv.apply_symm_apply _ _

/-- The inverse comparison recovers the same character-valued point. -/
@[simp]
theorem baseChangeCharacterPointsEquiv_baseChangeIso_inv (U : Over (Spec R'))
    (x : U ⟶ (groupScheme R' Λ).X) :
    baseChangeCharacterPointsEquiv b Λ U (x ≫ (baseChangeIso b Λ).inv.hom.hom) =
      characterPointsEquiv R' Λ U x := by
  have h := comp_isoOfPoints_inv
    (fun U => (baseChangeCharacterPointsEquiv b Λ U).trans
      (characterPointsEquiv R' Λ U).symm)
    (baseChangeIso_naturality b Λ) U x
  rw [show x ≫ (baseChangeIso b Λ).inv.hom.hom = _ from h]
  exact MulEquiv.apply_symm_apply _ _

/-- The same canonical comparison in the category of commutative group schemes. -/
def commBaseChangeIso :
    (CommGroupScheme.baseChange b).obj (groupScheme R Λ) ≅ groupScheme R' Λ where
  hom := Additive.ofMul (baseChangeIso b Λ).hom
  inv := Additive.ofMul (baseChangeIso b Λ).inv
  hom_inv_id := congrArg Additive.ofMul (baseChangeIso b Λ).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (baseChangeIso b Λ).inv_hom_id

end Langlands.GroupScheme.Diagonalizable
