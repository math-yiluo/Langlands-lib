import Mathlib.CategoryTheory.Center.Preadditive
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-! Evaluation of categorical centers at a fully faithful Hom object. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Preadditive C] (P : C)

/-- Evaluation at an object takes values in the center of its endomorphism ring. -/
def generatorCenterEvaluation : CatCenter C →+* Subring.center (End P) where
  toFun z := ⟨z.app P, Subring.mem_center_iff.mpr fun f => (CatCenter.naturality z f).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A faithful Hom functor detects a natural endomorphism from its generator component. -/
theorem generatorCenterEvaluation_injective [(preadditiveCoyonedaObj P).Faithful] :
    Function.Injective (generatorCenterEvaluation P) := by
  intro z w h
  have hP : z.app P = w.app P := congrArg Subtype.val h
  apply CatCenter.ext
  intro X
  apply (preadditiveCoyonedaObj P).map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change f ≫ z.app X = f ≫ w.app X
  rw [CatCenter.naturality z f, CatCenter.naturality w f, hP]

private def centralHomAction (c : Subring.center (End P)) (X : C) :
    (preadditiveCoyonedaObj P).obj X ⟶ (preadditiveCoyonedaObj P).obj X :=
  ModuleCat.ofHom
    { toFun := fun f => c.val ≫ f
      map_add' := fun f g => by simp only [Preadditive.comp_add]
      map_smul' := fun a f => by
        change c.val ≫ (a.unop ≫ f) = a.unop ≫ (c.val ≫ f)
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun k => k ≫ f) (Subring.mem_center_iff.mp c.property a.unop) }

private def centralHomLift [(preadditiveCoyonedaObj P).Full]
    (c : Subring.center (End P)) (X : C) : X ⟶ X :=
  (preadditiveCoyonedaObj P).preimage (centralHomAction P c X)

private theorem centralHomLift_comp [(preadditiveCoyonedaObj P).Full]
    (c : Subring.center (End P)) (X : C) (f : P ⟶ X) :
    f ≫ centralHomLift P c X = c.val ≫ f := by
  exact congrArg (fun k => k.hom f)
    ((preadditiveCoyonedaObj P).map_preimage (centralHomAction P c X))

/-- A full Hom functor lifts every central endomorphism to a natural endomorphism. -/
theorem generatorCenterEvaluation_surjective
    [(preadditiveCoyonedaObj P).Full] [(preadditiveCoyonedaObj P).Faithful] :
    Function.Surjective (generatorCenterEvaluation P) := by
  intro c
  let z : CatCenter C :=
    { app := centralHomLift P c
      naturality := fun X Y f => by
        apply (preadditiveCoyonedaObj P).map_injective
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        let g' : P ⟶ X := g
        change g' ≫ (f ≫ centralHomLift P c Y) = g' ≫ (centralHomLift P c X ≫ f)
        calc
          g' ≫ (f ≫ centralHomLift P c Y) =
              (g' ≫ f) ≫ centralHomLift P c Y := (Category.assoc _ _ _).symm
          _ = c.val ≫ (g' ≫ f) := centralHomLift_comp P c Y (g' ≫ f)
          _ = (c.val ≫ g') ≫ f := (Category.assoc _ _ _).symm
          _ = (g' ≫ centralHomLift P c X) ≫ f :=
            congrArg (fun k => k ≫ f) (centralHomLift_comp P c X g').symm
          _ = g' ≫ (centralHomLift P c X ≫ f) := Category.assoc _ _ _ }
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change centralHomLift P c P = c.val
  simpa using centralHomLift_comp P c P (𝟙 P)

/-- Evaluation identifies the categorical center with the endomorphism-ring center
whenever the Hom functor of the chosen object is fully faithful. -/
def generatorCenterEquiv
    [(preadditiveCoyonedaObj P).Full] [(preadditiveCoyonedaObj P).Faithful] :
    CatCenter C ≃+* Subring.center (End P) :=
  RingEquiv.ofBijective (generatorCenterEvaluation P)
    ⟨generatorCenterEvaluation_injective P, generatorCenterEvaluation_surjective P⟩

@[simp]
theorem generatorCenterEquiv_apply
    [(preadditiveCoyonedaObj P).Full] [(preadditiveCoyonedaObj P).Faithful]
    (z : CatCenter C) : (generatorCenterEquiv P z).val = z.app P := rfl

end Langlands.Renard
