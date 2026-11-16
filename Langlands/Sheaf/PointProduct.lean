import Langlands.Sheaf.Godement
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Products of skyscrapers with independent coefficients

The right adjoint to a family of actual site fibers takes an independent
coefficient object at each point to the product of its skyscraper sheaves.
The existing degree-zero Godement functor factors through this adjunction.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.PointProduct

open CategoryTheory CategoryTheory.Limits Opposite

universe wI w v u vA uA

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → GrothendieckTopology.Point.{w} J)
variable (A : Type uA) [Category.{vA} A]
variable [HasProducts.{w} A] [HasProducts.{wI} A]

/-- The product of the skyscrapers of an independently supplied coefficient family. -/
def productSheaf (M : I → A) : CategoryTheory.Sheaf J A :=
  ∏ᶜ fun i => (points i).skyscraperSheaf (M i)

/-- Functoriality of the product of skyscrapers in its coefficient family. -/
def productFunctor : (I → A) ⥤ CategoryTheory.Sheaf J A where
  obj := productSheaf points A
  map f := Limits.Pi.map fun i => (points i).skyscraperSheafFunctor.map (f i)
  map_id M := by
    dsimp [productSheaf]
    apply Pi.hom_ext
    intro i
    simp
  map_comp f g := by
    apply Pi.hom_ext
    intro i
    simp [Category.assoc, Pi.map_π, CategoryTheory.Pi.comp_apply]

/-- The coordinate projection of a product of skyscrapers. -/
abbrev projection (M : I → A) (i : I) :
    productSheaf points A M ⟶ (points i).skyscraperSheaf (M i) :=
  Pi.π _ i

@[reassoc (attr := simp)]
theorem productFunctor_map_projection {M N : I → A} (f : M ⟶ N) (i : I) :
    (productFunctor points A).map f ≫ projection points A N i =
    projection points A M i ≫ (points i).skyscraperSheafFunctor.map (f i) := by
  dsimp [productFunctor, projection]
  exact Pi.map_π _ _

variable [HasColimitsOfSize.{w, w} A]

/-- Collect all the actual site fibers into a family of coefficient objects. -/
def fiberFunctor : CategoryTheory.Sheaf J A ⥤ (I → A) :=
  Functor.pi' fun i => (points i).sheafFiber

/-- The product of the individual fiber/skyscraper hom equivalences. -/
def homEquiv (F : CategoryTheory.Sheaf J A) (M : I → A) :
    ((fiberFunctor points A).obj F ⟶ M) ≃
      (F ⟶ productSheaf points A M) where
  toFun f := Pi.lift fun i => (points i).skyscraperSheafAdjunction.homEquiv F (M i) (f i)
  invFun g i := ((points i).skyscraperSheafAdjunction.homEquiv F (M i)).symm
    (g ≫ projection points A M i)
  left_inv f := by
    funext i
    simp only [projection, Pi.lift_comp_π, Equiv.symm_apply_apply]
  right_inv g := by
    apply Pi.hom_ext
    intro i
    simp only [projection, Pi.lift_comp_π, Equiv.apply_symm_apply]

/-- Independent coefficient families are right adjoint to the family of actual fibers. -/
def adjunction : fiberFunctor points A ⊣ productFunctor points A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv points A
      homEquiv_naturality_left_symm f g := by
        funext i
        dsimp [homEquiv, fiberFunctor]
        simpa only [Category.assoc] using
          (points i).skyscraperSheafAdjunction.homEquiv_naturality_left_symm f
            (g ≫ projection points A _ i)
      homEquiv_naturality_right f g := by
        apply Pi.hom_ext
        intro i
        dsimp [homEquiv, productFunctor, projection]
        simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
        exact (points i).skyscraperSheafAdjunction.homEquiv_naturality_right (f i) (g i) }

instance : (productFunctor points A).IsRightAdjoint :=
  (adjunction points A).isRightAdjoint

/-- The existing degree-zero Godement functor is this adjunction's composite. -/
def godementZeroIso :
    Godement.zeroFunctor points A ≅ fiberFunctor points A ⋙ productFunctor points A :=
  NatIso.ofComponents
    (fun F => piObjIso (fun i => Godement.pointFunctor points A i) F)
    (by
      intro F F' f
      apply Pi.hom_ext
      intro i
      dsimp [fiberFunctor, productFunctor, projection]
      simp only [Category.assoc, Pi.map_π]
      change (Godement.zeroFunctor points A).map f ≫
          (piObjIso (fun i => Godement.pointFunctor points A i) F').hom ≫
            Pi.π (fun i => (Godement.pointFunctor points A i).obj F') i =
        (piObjIso (fun i => Godement.pointFunctor points A i) F).hom ≫
          Pi.π (fun i => (Godement.pointFunctor points A i).obj F) i ≫
            (Godement.pointFunctor points A i).map f
      rw [piObjIso_hom_comp_π, piObjIso_hom_comp_π_assoc]
      exact (Pi.π (fun i => Godement.pointFunctor points A i) i).naturality f)

/-- Sections of a product of skyscrapers are products over points and their fibers. -/
def sectionsIso (M : I → A) (X : C) :
    (productSheaf points A M).obj.obj (op X) ≅
      ∏ᶜ fun i => ∏ᶜ fun (_ : (points i).fiber.obj X) => M i :=
  PreservesProduct.iso
    (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op X))
    (fun i => (points i).skyscraperSheaf (M i))

/-- At a terminal object there is one coordinate for each site point. -/
def globalSectionsIso [LocallySmall.{w} C] (M : I → A) (X : C) (hX : IsTerminal X) :
    (productSheaf points A M).obj.obj (op X) ≅ ∏ᶜ M :=
  sectionsIso points A M X ≪≫ Pi.mapIso (fun i =>
    letI := (points i).uniqueFiberObj X hX
    productUniqueIso (fun (_ : (points i).fiber.obj X) => M i))

end Langlands.Sheaf.PointProduct
