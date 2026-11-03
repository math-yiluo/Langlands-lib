import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Dynamic.SchemeDecomposition

/-! # Levi-first multiplication for represented dynamic subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- Invert both coordinates and exchange them, as an isomorphism of schemes over the base. -/
def subgroupProductReversal (L U : GroupScheme S) : L.X ⊗ U.X ≅ U.X ⊗ L.X where
  hom := lift (snd L.X U.X)⁻¹ (fst L.X U.X)⁻¹
  inv := lift (snd U.X L.X)⁻¹ (fst U.X L.X)⁻¹
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [GrpObj.comp_inv]

variable {L U P : GroupScheme S}

/-- Reversal followed by reversed multiplication is multiplication followed by inversion. -/
theorem subgroupProductReversal_hom_comp_subgroupMultiplication (l : L ⟶ P) (r : U ⟶ P) :
    (subgroupProductReversal L U).hom ≫ subgroupMultiplication r l =
      subgroupMultiplication l r ≫ GrpObj.inv := by
  simp only [subgroupProductReversal, subgroupMultiplication, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc, GrpObj.inv_comp, GrpObj.inv_eq_inv,
    GrpObj.comp_inv, Category.comp_id, mul_inv_rev]

/-- The actual two-factor multiplication is an isomorphism in either order simultaneously. -/
theorem isIso_subgroupMultiplication_reverse_iff (l : L ⟶ P) (r : U ⟶ P) :
    IsIso (subgroupMultiplication l r) ↔ IsIso (subgroupMultiplication r l) := by
  have h :
      IsIso ((subgroupProductReversal L U).hom ≫ subgroupMultiplication r l) ↔
        IsIso (subgroupMultiplication l r ≫ GrpObj.inv) := by
    rw [subgroupProductReversal_hom_comp_subgroupMultiplication]
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h.symm

namespace Dynamic

variable {G : GroupScheme S} {χ : (Gm S).toGrp ⟶ G} [IsSeparated G.X.hom]
  {P Z U : GroupScheme S} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)
  (l : Z ⟶ P) (r : U ⟶ P) (hl : l ≫ iP = iZ) (hr : r ≫ iP = iU)

include hl hr in
omit [IsSeparated G.X.hom] in
/-- The reversed subgroup multiplication is the existing represented dynamic multiplication. -/
theorem subgroupMultiplication_eq_multiplication :
    subgroupMultiplication r l = multiplication hP hZ hU := by
  apply hP.1.right_cancellation
  rw [multiplication_comp, subgroupMultiplication, MonObj.mul_comp, Category.assoc,
    Category.assoc]
  have hl' := congrArg (fun f : Z ⟶ G => f.hom.hom) hl
  have hr' := congrArg (fun f : U ⟶ G => f.hom.hom) hr
  change l.hom.hom ≫ iP.hom.hom = iZ.hom.hom at hl'
  change r.hom.hom ≫ iP.hom.hom = iU.hom.hom at hr'
  rw [hl', hr']

include hP hZ hU hl hr in
/-- Every compatible pair of dynamic Levi and unipotent inclusions has Levi-first
multiplication an isomorphism of schemes over the base. -/
theorem isIso_subgroupMultiplication : IsIso (subgroupMultiplication l r) := by
  apply (isIso_subgroupMultiplication_reverse_iff l r).2
  rw [subgroupMultiplication_eq_multiplication hP hZ hU l r hl hr]
  exact isIso_multiplication hP hZ hU

/-- The actual Levi-first multiplication isomorphism for any compatible represented
centralizer and unipotent subgroup of a represented dynamic parabolic. -/
def leviMultiplicationIso : Z.X ⊗ U.X ≅ P.X :=
  haveI := isIso_subgroupMultiplication hP hZ hU l r hl hr
  asIso (subgroupMultiplication l r)

@[simp]
theorem leviMultiplicationIso_hom :
    (leviMultiplicationIso hP hZ hU l r hl hr).hom = subgroupMultiplication l r := rfl

end Dynamic

end Langlands.GroupScheme
