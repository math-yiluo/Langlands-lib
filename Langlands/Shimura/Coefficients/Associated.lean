import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Action.Basic

/-! # Associated coefficient sheaves as actual invariants over a cover

The construction is defined for a genuine object with a group action on a
site with binary products. A torsor hypothesis is needed for local triviality,
not for forming this invariant sheaf.
-/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R]

/-- The actual sheaf `U ↦ F(Y × U)`, obtained using localization of the site. -/
def productSheaf (Y : C) :
    Sheaf J (ModuleCat.{u} R) ⥤ Sheaf J (ModuleCat.{u} R) :=
  J.overPullback (ModuleCat.{u} R) Y ⋙
    (Over.star Y).sheafPushforwardContinuous (ModuleCat.{u} R) J (J.over Y)

/-- Pullback of sections along an endomorphism of the cover object. -/
def deckMap {Y : C} (a : Y ⟶ Y) (F : Sheaf J (ModuleCat.{u} R)) :
    (productSheaf J Y).obj F ⟶ (productSheaf J Y).obj F where
  hom.app U := F.obj.map (prod.map a (𝟙 U.unop)).op
  hom.naturality := by
    intro U V f
    change F.obj.map (prod.map (𝟙 Y) f.unop).op ≫
        F.obj.map (prod.map a (𝟙 V.unop)).op =
      F.obj.map (prod.map a (𝟙 U.unop)).op ≫
        F.obj.map (prod.map (𝟙 Y) f.unop).op
    simp only [← Functor.map_comp, ← op_comp, prod.map_map,
      Category.id_comp, Category.comp_id]

@[simp] theorem deckMap_id (Y : C) (F : Sheaf J (ModuleCat.{u} R)) :
    deckMap J (𝟙 Y) F = 𝟙 ((productSheaf J Y).obj F) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map (𝟙 Y) (𝟙 U.unop)).op = 𝟙 _
  simp

@[reassoc] theorem deckMap_comp {Y : C} (a b : Y ⟶ Y)
    (F : Sheaf J (ModuleCat.{u} R)) :
    deckMap J (a ≫ b) F = deckMap J b F ≫ deckMap J a F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map (a ≫ b) (𝟙 U.unop)).op =
    F.obj.map (prod.map b (𝟙 U.unop)).op ≫ F.obj.map (prod.map a (𝟙 U.unop)).op
  rw [← F.obj.map_comp, ← op_comp, prod.map_map, Category.id_comp]

@[reassoc] theorem deckMap_natural {Y : C} (a : Y ⟶ Y)
    {F F' : Sheaf J (ModuleCat.{u} R)} (f : F ⟶ F') :
    deckMap J a F ≫ (productSheaf J Y).map f =
      (productSheaf J Y).map f ≫ deckMap J a F' := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  exact f.hom.naturality _

variable {G : Type u} [Group G] (Y : Action C G)

local instance : HasLimitsOfShape (SingleObj G) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

/-- The diagonal action: coefficient action together with inverse deck pullback. -/
def diagonal (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    Action (Sheaf J (ModuleCat.{u} R)) G where
  V := (productSheaf J Y.V).obj F.V
  ρ :=
    { toFun g := deckMap J (Y.ρ g⁻¹) F.V ≫ (productSheaf J Y.V).map (F.ρ g)
      map_one' := by simp
      map_mul' g h := by
        change deckMap J (Y.ρ (g * h)⁻¹) F.V ≫
            (productSheaf J Y.V).map (F.ρ (g * h)) =
          (deckMap J (Y.ρ h⁻¹) F.V ≫ (productSheaf J Y.V).map (F.ρ h)) ≫
            (deckMap J (Y.ρ g⁻¹) F.V ≫ (productSheaf J Y.V).map (F.ρ g))
        simp only [mul_inv_rev, map_mul, End.mul_def]
        rw [deckMap_comp, Functor.map_comp]
        simp only [Category.assoc]
        rw [deckMap_natural_assoc] }

/-- Equivariant coefficient morphisms induce equivariant maps before taking invariants. -/
def diagonalFunctor :
    Action (Sheaf J (ModuleCat.{u} R)) G ⥤
      Action (Sheaf J (ModuleCat.{u} R)) G where
  obj F := diagonal J Y F
  map f :=
    { hom := (productSheaf J Y.V).map f.hom
      comm g := by
        change (deckMap J (Y.ρ g⁻¹) _ ≫ (productSheaf J Y.V).map _) ≫ _ =
          _ ≫ (deckMap J (Y.ρ g⁻¹) _ ≫ (productSheaf J Y.V).map _)
        rw [Category.assoc, ← Functor.map_comp, f.comm,
          Functor.map_comp, ← Category.assoc, deckMap_natural, Category.assoc] }
  map_id F := by
    apply Action.hom_injective
    exact (productSheaf J Y.V).map_id F.V
  map_comp f g := by
    apply Action.hom_injective
    exact (productSheaf J Y.V).map_comp f.hom g.hom

/-- The actual diagram whose limit is the invariant sheaf. -/
def invariantDiagram :
    Action (Sheaf J (ModuleCat.{u} R)) G ⥤
      (SingleObj G ⥤ Sheaf J (ModuleCat.{u} R)) :=
  diagonalFunctor J Y ⋙
    (Action.functorCategoryEquivalence (Sheaf J (ModuleCat.{u} R)) G).functor

/-- The associated sheaf functor is the categorical invariant subsheaf. -/
def associatedFunctor :
    Action (Sheaf J (ModuleCat.{u} R)) G ⥤ Sheaf J (ModuleCat.{u} R) :=
  invariantDiagram J Y ⋙ lim

/-- The invariant sheaf for the given cover action and coefficient action. -/
abbrev associated (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    Sheaf J (ModuleCat.{u} R) :=
  (associatedFunctor J Y).obj F

/-- Inclusion of the invariant sheaf into the sheaf of sections over the cover. -/
def inclusion (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    associated J Y F ⟶ (productSheaf J Y.V).obj F.V :=
  limit.π ((invariantDiagram J Y).obj F) (SingleObj.star G)

@[reassoc] theorem inclusion_invariant (F : Action (Sheaf J (ModuleCat.{u} R)) G)
    (g : G) :
    inclusion J Y F ≫ (diagonal J Y F).ρ g = inclusion J Y F :=
  limit.w ((invariantDiagram J Y).obj F) g

@[reassoc] theorem inclusion_natural
    {F F' : Action (Sheaf J (ModuleCat.{u} R)) G} (f : F ⟶ F') :
    (associatedFunctor J Y).map f ≫ inclusion J Y F' =
      inclusion J Y F ≫ (productSheaf J Y.V).map f.hom :=
  limit.map_π ((invariantDiagram J Y).map f) (SingleObj.star G)

/-- Construct a map to the associated sheaf from any invariant map over the cover. -/
def lift {F : Action (Sheaf J (ModuleCat.{u} R)) G}
    {T : Sheaf J (ModuleCat.{u} R)}
    (f : T ⟶ (productSheaf J Y.V).obj F.V)
    (hf : ∀ g : G, f ≫ (diagonal J Y F).ρ g = f) :
    T ⟶ associated J Y F :=
  limit.lift ((invariantDiagram J Y).obj F)
    { pt := T
      π := { app := fun _ => f
             naturality := fun _ _ g => by
               change (𝟙 T) ≫ f = f ≫ (diagonal J Y F).ρ g
               rw [Category.id_comp, hf] } }

@[reassoc (attr := simp)] theorem lift_inclusion
    {F : Action (Sheaf J (ModuleCat.{u} R)) G} {T : Sheaf J (ModuleCat.{u} R)}
    (f : T ⟶ (productSheaf J Y.V).obj F.V)
    (hf : ∀ g : G, f ≫ (diagonal J Y F).ρ g = f) :
    lift J Y f hf ≫ inclusion J Y F = f :=
  limit.lift_π _ _

theorem hom_ext {F : Action (Sheaf J (ModuleCat.{u} R)) G}
    {T : Sheaf J (ModuleCat.{u} R)} {f g : T ⟶ associated J Y F}
    (h : f ≫ inclusion J Y F = g ≫ inclusion J Y F) : f = g := by
  apply limit.hom_ext
  rintro ⟨⟩
  exact h

instance inclusion_mono (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    Mono (inclusion J Y F) where
  right_cancellation f g h := hom_ext J Y (f := f) (g := g) h

/-- Constant module coefficients acquire the same genuine descent construction. -/
def constantAssociatedFunctor [HasSheafify J (ModuleCat.{u} R)] :
    Action (ModuleCat.{u} R) G ⥤ Sheaf J (ModuleCat.{u} R) :=
  (constantSheaf J (ModuleCat.{u} R)).mapAction G ⋙ associatedFunctor J Y

end Langlands.Shimura.Coefficients
