import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Sheaves.Sheafify

/-! # Constant module sheaf germs and actual stalk images -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.ModuleSheaf

open CategoryTheory TopologicalSpace

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- The actual germ at a point of a constant vector in the constant module sheaf. -/
def constantSheafGerm (V : ModuleCat.{u} R) (x : X) :
    V ⟶ TopCat.Presheaf.stalk
      (((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj V).obj) x :=
  (toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj V)).app
    (.op ⊤) ≫ TopCat.Presheaf.Γgerm
      (((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj V).obj) x

/-- Every actual stalk element of a constant module sheaf is a constant-vector germ. -/
theorem constantSheafGerm_surjective (V : ModuleCat.{u} R) (x : X) :
    Function.Surjective (constantSheafGerm V x) := by
  let P := (Functor.const (Opens X)ᵒᵖ).obj V
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x
  let j := toSheafify (Opens.grothendieckTopology X) P
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x
    (ModuleCat.{u} R) P
  intro v
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map j)).surjective v
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq P a
  refine ⟨s, ?_⟩
  have hg : TopCat.Presheaf.germ P U x hx s = TopCat.Presheaf.Γgerm P x s := by
    exact TopCat.Presheaf.Γgerm_res_apply P (i := homOfLE le_top) x hx s
  rw [hg]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x (Set.mem_univ x) j s).symm

/-- The stalk image of a map out of a constant sheaf is the range on constant vectors. -/
theorem constantSheaf_stalk_range (V : ModuleCat.{u} R)
    {M : X.Sheaf (ModuleCat.{u} R)}
    (f : (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj V ⟶ M)
    (x : X) :
    LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f.hom).hom =
      LinearMap.range ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj V)).app (.op ⊤) ≫
          f.hom.app (.op ⊤) ≫ TopCat.Presheaf.Γgerm M.obj x).hom := by
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x
  have e : constantSheafGerm V x ≫ T.map f.hom =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj V)).app (.op ⊤) ≫
          f.hom.app (.op ⊤) ≫ TopCat.Presheaf.Γgerm M.obj x := by
    rw [constantSheafGerm, Category.assoc]
    exact congrArg (fun k => (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj V)).app (.op ⊤) ≫ k)
      (TopCat.Presheaf.stalkFunctor_map_germ ⊤ x (Set.mem_univ x) f.hom)
  rw [← e]
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := constantSheafGerm_surjective V x a
    exact ⟨b, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨constantSheafGerm V x a, rfl⟩

end Langlands.ModuleSheaf
