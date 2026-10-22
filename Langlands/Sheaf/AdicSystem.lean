import Langlands.Coefficients.AdicSystem
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Ideal-adic systems of sheaves

The reductions are obtained by quotienting the section modules and then
sheafifying. Their maps and inverse systems are actual categorical functors.
This does not identify a constant coefficient system with a descended local
system on a Shimura variety.
-/

noncomputable section

namespace Langlands.Sheaf.AdicSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe u v uC vC w

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R] (I : Ideal R)

variable [HasSheafify J (ModuleCat.{v} R)]

/-- Sheafify sectionwise coefficient reduction from `R` to `R / I`. -/
def quotientCoefficients [HasSheafify J (ModuleCat.{v} (R ⧸ I))] :
    CategoryTheory.Sheaf J (ModuleCat.{v} R) ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} (R ⧸ I)) :=
  sheafToPresheaf J (ModuleCat.{v} R) ⋙
    (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{v} R) (ModuleCat.{v} (R ⧸ I))).obj
      (Langlands.Coefficients.AdicSystem.reduction I) ⋙
    presheafToSheaf J (ModuleCat.{v} (R ⧸ I))

/-- Extend a module endofunctor to sheaves by sectionwise application and sheafification. -/
def sheafifyEndofunctor :
    ((ModuleCat.{v} R) ⥤ (ModuleCat.{v} R)) ⥤ (CategoryTheory.Sheaf J (ModuleCat.{v} R) ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R)) :=
  Functor.whiskeringRight Cᵒᵖ (ModuleCat.{v} R) (ModuleCat.{v} R) ⋙
    (Functor.whiskeringLeft (CategoryTheory.Sheaf J (ModuleCat.{v} R))
      (Cᵒᵖ ⥤ (ModuleCat.{v} R)) (Cᵒᵖ ⥤ (ModuleCat.{v} R))).obj (sheafToPresheaf J (ModuleCat.{v} R)) ⋙
    (Functor.whiskeringRight (CategoryTheory.Sheaf J (ModuleCat.{v} R))
      (Cᵒᵖ ⥤ (ModuleCat.{v} R)) (CategoryTheory.Sheaf J (ModuleCat.{v} R))).obj (presheafToSheaf J (ModuleCat.{v} R))

/-- The inverse system of sheaf reduction endofunctors. -/
def powers : ℕᵒᵖ ⥤ (CategoryTheory.Sheaf J (ModuleCat.{v} R) ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R)) :=
  Langlands.Coefficients.AdicSystem.powers I ⋙ sheafifyEndofunctor J

/-- Functorial ideal-adic reduction of a sheaf. -/
def functor : CategoryTheory.Sheaf J (ModuleCat.{v} R) ⥤ (ℕᵒᵖ ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R)) :=
  (powers J I).flip

/-- All reductions and transitions for a given sheaf. -/
abbrev system (F : CategoryTheory.Sheaf J (ModuleCat.{v} R)) : ℕᵒᵖ ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R) :=
  (functor J I).obj F

/-- The canonical quotient map, using the inverse sheafification counit. -/
def quotientMap (n : ℕ) :
    𝟭 (CategoryTheory.Sheaf J (ModuleCat.{v} R)) ⟶ (powers J I).obj (op n) :=
  inv (sheafificationAdjunction J (ModuleCat.{v} R)).counit ≫
    (sheafifyEndofunctor J).map (Langlands.Coefficients.AdicSystem.quotientMap I n)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem quotientMap_transition {m n : ℕ} (h : m ≤ n) :
    quotientMap J I n ≫ (powers J I).map (homOfLE h).op = quotientMap J I m := by
  change (inv (sheafificationAdjunction J (ModuleCat.{v} R)).counit ≫
      (sheafifyEndofunctor J).map (Langlands.Coefficients.AdicSystem.quotientMap I n)) ≫
      (sheafifyEndofunctor J).map (Langlands.Coefficients.AdicSystem.transition I h) =
    inv (sheafificationAdjunction J (ModuleCat.{v} R)).counit ≫
      (sheafifyEndofunctor J).map (Langlands.Coefficients.AdicSystem.quotientMap I m)
  rw [Category.assoc, ← Functor.map_comp,
    Langlands.Coefficients.AdicSystem.quotientMap_transition]

/-- (ModuleCat.{v} R) constant-coefficient system formed from the actual reductions of a module. -/
def constantSystemFunctor : (ModuleCat.{v} R) ⥤ (ℕᵒᵖ ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R)) :=
  Langlands.Coefficients.AdicSystem.functor I ⋙
    (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{v} R) (CategoryTheory.Sheaf J (ModuleCat.{v} R))).obj (constantSheaf J (ModuleCat.{v} R))

/-- The sheaf inverse system for a constant coefficient module. -/
abbrev constantSystem (M : (ModuleCat.{v} R)) : ℕᵒᵖ ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R) :=
  (constantSystemFunctor J I).obj M

/-- The inverse-limit sheaf of the constructed ideal-adic reductions. -/
def inverseLimit (F : CategoryTheory.Sheaf J (ModuleCat.{v} R)) : CategoryTheory.Sheaf J (ModuleCat.{v} R) :=
  limit (system J I F)

/-- Projection from the limit sheaf to a coefficient level. -/
def projection (F : CategoryTheory.Sheaf J (ModuleCat.{v} R)) (n : ℕ) :
    inverseLimit J I F ⟶ (system J I F).obj (op n) :=
  limit.π _ (op n)

/-- Algebraic actions on a sheaf are transported to its entire coefficient system. -/
def actionFunctor (G : Type w) [Monoid G] :
    Action (CategoryTheory.Sheaf J (ModuleCat.{v} R)) G ⥤
      Action (ℕᵒᵖ ⥤ CategoryTheory.Sheaf J (ModuleCat.{v} R)) G :=
  (functor J I).mapAction G

end Langlands.Sheaf.AdicSystem
