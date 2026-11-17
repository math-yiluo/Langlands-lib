import Langlands.AlgebraicGeometry.LocallyNoetherianComponentCoproduct
import Langlands.AbelianScheme.GroupScheme

/-! # Relative morphisms that are constant on actual connected components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.AlgebraicGeometry.ComponentConstant

variable {S : Scheme.{u}} (X : Over S) {Y Z : Over S}
  [IsLocallyNoetherian X.left]

/-- Glue a chosen base section on each actual open connected-component scheme. -/
def ofComponents
    (s : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Y)) : X ⟶ Y :=
  Over.homMk
    (componentDesc X.left (fun c =>
      componentι X.left c ≫ X.hom ≫ (s c).left))
    (by
      apply component_hom_ext X.left
      intro c
      simp only [Category.assoc, componentι_componentDesc_assoc, Over.w]
      exact Category.comp_id (componentι X.left c ≫ X.hom))

@[reassoc (attr := simp)]
theorem componentι_ofComponents
    (s : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Y))
    (c : _root_.ConnectedComponents X.left) :
    componentι X.left c ≫ (ofComponents X s).left =
      componentι X.left c ≫ X.hom ≫ (s c).left := by
  simp only [ofComponents, Over.homMk_left, componentι_componentDesc]

/-- A single base section gives the usual constant relative morphism. -/
theorem ofComponents_const (s : Over.mk (𝟙 S) ⟶ Y) :
    ofComponents X (fun _ => s) = toUnit X ≫ s := by
  apply Over.OverMorphism.ext
  apply component_hom_ext X.left
  intro c
  simp only [componentι_ofComponents, Over.comp_left]
  rfl

/-- The glued construction commutes with arbitrary postcomposition. -/
theorem ofComponents_postcomp
    (s : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Y))
    (f : Y ⟶ Z) :
    ofComponents X s ≫ f = ofComponents X (fun c => s c ≫ f) := by
  apply Over.OverMorphism.ext
  apply component_hom_ext X.left
  intro c
  simp only [Over.comp_left, componentι_ofComponents_assoc,
    componentι_ofComponents]

variable {X}

/-- Precomposition transports the family along the actual map of components. -/
theorem precomp_ofComponents {X' : Over S} [IsLocallyNoetherian X'.left]
    (f : X' ⟶ X)
    (s : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Y)) :
    f ≫ ofComponents X s =
      ofComponents X' (fun c => s (componentMap f.left c)) := by
  apply Over.OverMorphism.ext
  apply component_hom_ext X'.left
  intro c
  simp only [Over.comp_left, componentι_ofComponents]
  calc
    componentι X'.left c ≫ f.left ≫ (ofComponents X s).left =
        componentHom f.left c ≫ componentι X.left (componentMap f.left c) ≫
          (ofComponents X s).left := by
      rw [componentHom_ι_assoc]
    _ = componentHom f.left c ≫ componentι X.left (componentMap f.left c) ≫
        X.hom ≫ (s (componentMap f.left c)).left := by
      rw [componentι_ofComponents]
    _ = componentι X'.left c ≫ X'.hom ≫ (s (componentMap f.left c)).left := by
      rw [componentHom_ι_assoc, Over.w_assoc f]

variable (X)

/-- Pairing two componentwise constant morphisms is componentwise constant. -/
theorem lift_ofComponents
    (s : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Y))
    (t : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Z)) :
    lift (ofComponents X s) (ofComponents X t) =
      ofComponents X (fun c => lift (s c) (t c)) := by
  apply hom_ext
  · rw [lift_fst, ofComponents_postcomp]
    simp only [lift_fst]
  · rw [lift_snd, ofComponents_postcomp]
    simp only [lift_snd]

/-- An actual morphism is componentwise constant if it comes from base sections
on the actual open component schemes. -/
def IsComponentConstant (f : X ⟶ Y) : Prop :=
  ∃ s : _root_.ConnectedComponents X.left → (Over.mk (𝟙 S) ⟶ Y),
    f = ofComponents X s

variable {X}

theorem IsComponentConstant.precomp {f : X ⟶ Y} (hf : IsComponentConstant X f)
    {X' : Over S} [IsLocallyNoetherian X'.left] (g : X' ⟶ X) :
    IsComponentConstant X' (g ≫ f) := by
  obtain ⟨s, rfl⟩ := hf
  exact ⟨_, precomp_ofComponents g s⟩

theorem IsComponentConstant.postcomp {f : X ⟶ Y} (hf : IsComponentConstant X f)
    (g : Y ⟶ Z) : IsComponentConstant X (f ≫ g) := by
  obtain ⟨s, rfl⟩ := hf
  exact ⟨_, ofComponents_postcomp X s g⟩

theorem IsComponentConstant.lift {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : IsComponentConstant X f) (hg : IsComponentConstant X g) :
    IsComponentConstant X (lift f g) := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨t, rfl⟩ := hg
  exact ⟨_, lift_ofComponents X s t⟩

end Langlands.AlgebraicGeometry.ComponentConstant
