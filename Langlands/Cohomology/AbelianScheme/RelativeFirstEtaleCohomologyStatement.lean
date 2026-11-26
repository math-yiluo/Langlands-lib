import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Tate.PrimeAdic
import Langlands.AbelianScheme.Tate.TestScheme
import Langlands.Geometry.EtaleDerivedDirectImage
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Relative first étale cohomology and the character sheaf of torsion

The finite-coefficient relative comparison underlying Harris–Taylor
III.2, p. 98. The character presheaf uses morphisms of the actual module
sheaves restricted to each slice.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.AbelianFirstEtale

open Langlands.GroupScheme.Tate

variable {S : Scheme.{0}} (A : Langlands.AbelianScheme S) (n : ℕ)

private abbrev forgetEtale : S.Etale ⥤ Over S :=
  MorphismProperty.Over.forget (@Etale) ⊤ S

private def torsionSections : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod n) where
  obj U := ModuleCat.of (ZMod n) (Level A.toGrp (forgetEtale.obj U.unop) n)
  map a := ModuleCat.ofHom
    { toAddHom := levelRestrict A.toGrp (forgetEtale.map a.unop) n
      map_smul' := by
        intro c x
        obtain ⟨b, rfl⟩ := ZMod.intCast_surjective c
        change levelRestrict A.toGrp (forgetEtale.map a.unop) n ((b : ZMod n) • x) =
          (b : ZMod n) • levelRestrict A.toGrp (forgetEtale.map a.unop) n x
        simp only [Int.cast_smul_eq_zsmul, map_zsmul] }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply toSection_injective
    apply Additive.toMul.injective
    change Additive.toMul (toSection A.toGrp _ n
      (levelRestrict A.toGrp (forgetEtale.map (𝟙 U).unop) n x)) =
      Additive.toMul (toSection A.toGrp _ n x)
    rw [toSection_levelRestrict, unop_id, (forgetEtale (S := S)).map_id, Category.id_comp]
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply toSection_injective
    apply Additive.toMul.injective
    change Additive.toMul (toSection A.toGrp _ n
      (levelRestrict A.toGrp (forgetEtale.map (a ≫ b).unop) n x)) =
      Additive.toMul (toSection A.toGrp _ n
        (levelRestrict A.toGrp (forgetEtale.map b.unop) n
          (levelRestrict A.toGrp (forgetEtale.map a.unop) n x)))
    simp only [toSection_levelRestrict, unop_comp, Functor.map_comp, Category.assoc]

/-- The sheaf of finite torsion sections, defined by sheafifying the
actual section presheaf of the multiplication kernel. -/
def torsionModuleSheaf : EtaleDerivedSections.ModuleSheaf S (ZMod n) :=
  (presheafToSheaf S.smallEtaleTopology (ModuleCat (ZMod n))).obj (torsionSections A n)

private def constantCoefficients (X : Scheme.{0}) (n : ℕ) :
    EtaleDerivedSections.ModuleSheaf X (ZMod n) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{0} (ZMod n))).obj
    (ModuleCat.of (ZMod n) (ZMod n))

private def characterValues : S.Etaleᵒᵖ ⥤ Type 1 :=
  presheafHom (torsionModuleSheaf A n).obj (constantCoefficients S n).obj

instance characterValues_addCommGroup (U : S.Etaleᵒᵖ) :
    AddCommGroup ((characterValues A n).obj U) :=
  inferInstanceAs (AddCommGroup
    ((Over.forget U.unop).op ⋙ (torsionModuleSheaf A n).obj ⟶
      (Over.forget U.unop).op ⋙ (constantCoefficients S n).obj))

instance characterValues_module (U : S.Etaleᵒᵖ) :
    Module (ZMod n) ((characterValues A n).obj U) :=
  inferInstanceAs (Module (ZMod n)
    ((Over.forget U.unop).op ⋙ (torsionModuleSheaf A n).obj ⟶
      (Over.forget U.unop).op ⋙ (constantCoefficients S n).obj))

/-- The internal character presheaf at an étale test object is the module
of linear maps from the restriction of the torsion sheaf to the
constant coefficient sheaf. The relevant Hom size is one universe larger. -/
def torsionCharacterPresheaf : S.Etaleᵒᵖ ⥤ ModuleCat.{1} (ZMod n) where
  obj U := ModuleCat.of (ZMod n) ((characterValues A n).obj U)
  map a := ModuleCat.ofHom
    { toFun := (characterValues A n).map a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (characterValues A n).map_id_apply U x
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (characterValues A n).map_comp_apply a b x

/-- The constructed module-valued character presheaf satisfies the sheaf
condition, since its underlying type presheaf is the internal Hom. -/
theorem torsionCharacterPresheaf_isSheaf :
    Presheaf.IsSheaf S.smallEtaleTopology (torsionCharacterPresheaf A n) := by
  let : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ZMod n))) :=
    reflectsLimitsOfSize_of_univLE.{1, 1} _
  refine Presheaf.isSheaf_of_isSheaf_comp S.smallEtaleTopology
    (torsionCharacterPresheaf A n) (forget (ModuleCat.{1} (ZMod n))) ?_
  change Presheaf.IsSheaf S.smallEtaleTopology (characterValues A n)
  exact (constantCoefficients S n).property.hom (torsionModuleSheaf A n).obj

/-- When `n` is positive and invertible on the base, the relative first
étale cohomology of an abelian scheme with coefficients `ℤ/nℤ` is the
internal character sheaf of its `n`-torsion. An isomorphism of the
underlying module-valued presheaves expresses the sheaf comparison. -/
def RelativeFirstEtaleCohomologyStatement : Prop :=
  0 < n → IsUnit (n : Γ(S, ⊤)) →
  let higherImage := (EtaleDerivedDirectImage.higherDirectImage A.X.hom (ZMod n) 1).obj
    (constantCoefficients A.X.left n)
  Nonempty (higherImage.obj ⋙ ModuleCat.uliftFunctor.{1} (ZMod n) ≅
    torsionCharacterPresheaf A n)

end Langlands.Cohomology.AbelianFirstEtale
