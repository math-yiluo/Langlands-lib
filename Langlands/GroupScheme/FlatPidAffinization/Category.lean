import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! # The Cartesian category of flat quasi-compact separated schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.FlatPidAffinization

/-- The objects on which canonical affinization will preserve finite products over a PID. -/
def flatQcSeparated (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X => Flat X.hom ∧ QuasiCompact X.hom ∧ IsSeparated X.hom

instance (S : Scheme.{u}) : (flatQcSeparated S).IsMonoidal where
  prop_unit := by
    change Flat (𝟙 S) ∧ QuasiCompact (𝟙 S) ∧ IsSeparated (𝟙 S)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  prop_tensor X Y hX hY := by
    rcases hX with ⟨hXF, hXQ, hXS⟩
    rcases hY with ⟨hYF, hYQ, hYS⟩
    change Flat (pullback.fst X.hom Y.hom ≫ X.hom) ∧
      QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom) ∧
      IsSeparated (pullback.fst X.hom Y.hom ≫ X.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Flat quasi-compact separated schemes over a fixed base, with all base morphisms. -/
abbrev SchemeCategory (S : Scheme.{u}) := (flatQcSeparated S).FullSubcategory

instance (S : Scheme.{u}) : CartesianMonoidalCategory (SchemeCategory S) where
  __ := ObjectProperty.fullMonoidalSubcategory (flatQcSeparated S)
  isTerminalTensorUnit := .ofUniqueHom (fun X => ObjectProperty.homMk (toUnit X.1))
    fun _ _ => ObjectProperty.hom_ext _ (toUnit_unique _ _)
  fst X Y := ObjectProperty.homMk (fst X.1 Y.1)
  snd X Y := ObjectProperty.homMk (snd X.1 Y.1)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g => ObjectProperty.homMk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def X Y := ObjectProperty.hom_ext _ (fst_def X.1 Y.1)
  snd_def X Y := ObjectProperty.hom_ext _ (snd_def X.1 Y.1)

/-- The full inclusion of the flat quasi-compact separated category. -/
abbrev inclusion (S : Scheme.{u}) : SchemeCategory S ⥤ Over S := (flatQcSeparated S).ι

/-- An actual group scheme satisfying the geometric hypotheses, regarded in the full subcategory. -/
def restrictedGroup {S : Scheme.{u}} (G : GroupScheme S)
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] : Grp (SchemeCategory S) := by
  let X : SchemeCategory S := ⟨G.X, inferInstance, inferInstance, inferInstance⟩
  letI : GrpObj ((inclusion S).obj X) := G.grp
  letI : GrpObj X := (flatQcSeparated S).fullyFaithfulι.grpObj X
  exact Grp.mk X

/-- Forgetting the geometric restriction recovers the original group scheme. -/
def restrictedGroupIso {S : Scheme.{u}} (G : GroupScheme S)
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    (inclusion S).mapGrp.obj (restrictedGroup G) ≅ G := by
  refine Grp.mkIso (Iso.refl _) ?_ ?_
  · change (𝟙 _ ≫ (𝟙 _ ≫ MonObj.one)) ≫ 𝟙 _ = MonObj.one
    simp
  · change (𝟙 _ ≫ (𝟙 _ ≫ MonObj.mul)) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ MonObj.mul
    simp

@[simp] theorem restrictedGroupIso_hom_left {S : Scheme.{u}} (G : GroupScheme S)
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    (restrictedGroupIso G).hom.hom.hom.left = 𝟙 G.X.left := rfl

end Langlands.GroupScheme.FlatPidAffinization
