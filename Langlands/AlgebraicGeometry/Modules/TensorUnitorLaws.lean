import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Naturality of the explicit sheaf tensor unitors -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

open MonoidalCategory

variable {X : Scheme.{u}}

local instance tensorUnitorLawsMonoidal : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

lemma tensorLeftUnitor_naturality {M N : X.Modules} (f : M ⟶ N) :
    tensorMap (𝟙 (structureSheaf X)) f ≫ (tensorLeftUnitor N).hom =
      (tensorLeftUnitor M).hom ≫ f := by
  change (sheafify X).map ((𝟙 _) ⊗ₘ f.val) ≫
      ((sheafify X).map (λ_ N.val).hom ≫ (sheafifyForgetIso X).hom.app N) =
    ((sheafify X).map (λ_ M.val).hom ≫ (sheafifyForgetIso X).hom.app M) ≫ f
  erw [← Category.assoc, ← Functor.map_comp, id_tensorHom, leftUnitor_naturality,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((sheafify X).map (λ_ M.val).hom ≫ ·)
    ((sheafifyForgetIso X).hom.naturality f)

lemma tensorRightUnitor_naturality {M N : X.Modules} (f : M ⟶ N) :
    tensorMap f (𝟙 (structureSheaf X)) ≫ (tensorRightUnitor N).hom =
      (tensorRightUnitor M).hom ≫ f := by
  change (sheafify X).map (f.val ⊗ₘ (𝟙 _)) ≫
      ((sheafify X).map (ρ_ N.val).hom ≫ (sheafifyForgetIso X).hom.app N) =
    ((sheafify X).map (ρ_ M.val).hom ≫ (sheafifyForgetIso X).hom.app M) ≫ f
  erw [← Category.assoc, ← Functor.map_comp, tensorHom_id, rightUnitor_naturality,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((sheafify X).map (ρ_ M.val).hom ≫ ·)
    ((sheafifyForgetIso X).hom.naturality f)

lemma tensorUnitors_equal (X : Scheme.{u}) :
    (tensorLeftUnitor (structureSheaf X)).hom =
      (tensorRightUnitor (structureSheaf X)).hom := by
  change (sheafify X).map (λ_ (𝟙_ X.PresheafOfModules)).hom ≫
      (sheafifyForgetIso X).hom.app (structureSheaf X) =
    (sheafify X).map (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫
      (sheafifyForgetIso X).hom.app (structureSheaf X)
  erw [unitors_equal]

end Langlands.Scheme.Modules
