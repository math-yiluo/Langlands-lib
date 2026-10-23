import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! # Tensor products of module sheaves on schemes -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory BraidedCategory
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u})

local instance : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

local instance : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

/-- Module sheafification over the unchanged structure sheaf. -/
def sheafify : X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheafification adjunction over a scheme. -/
def sheafifyAdjunction : sheafify X ⊣ Scheme.Modules.toPresheafOfModules X :=
  PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

/-- Sheafifying the underlying presheaf of a module sheaf returns that sheaf. -/
def sheafifyForgetIso :
    Scheme.Modules.toPresheafOfModules X ⋙ sheafify X ≅ 𝟭 X.Modules :=
  asIso (sheafifyAdjunction X).counit

/-- Tensor product of module sheaves, formed by sheafifying the sectionwise tensor. -/
def tensorFunctor : X.Modules × X.Modules ⥤ X.Modules :=
  (Scheme.Modules.toPresheafOfModules X).prod (Scheme.Modules.toPresheafOfModules X) ⋙
    tensor X.PresheafOfModules ⋙ sheafify X

variable {X}

/-- The tensor product object of two module sheaves on a scheme. -/
abbrev tensorObj (M N : X.Modules) : X.Modules :=
  (tensorFunctor X).obj (M, N)

/-- Explicit comparison with sheafification of the sectionwise tensor product. -/
def tensorSheafificationIso (M N : X.Modules) :
    tensorObj M N ≅ (sheafify X).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := X.presheaf) M.val N.val) :=
  Iso.refl _

/-- The tensor product of morphisms of module sheaves. -/
abbrev tensorMap {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M' N' :=
  (tensorFunctor X).map (f, g)

/-- The structure sheaf considered as a module over itself. -/
def structureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Maps out of the sheaf tensor correspond to presheaf maps out of the sectionwise tensor. -/
def tensorHomEquiv (M N P : X.Modules) :
    (tensorObj M N ⟶ P) ≃ (M.val ⊗ N.val ⟶ P.val) :=
  (sheafifyAdjunction X).homEquiv _ P

/-- The symmetry isomorphism induced by swapping the presheaf tensor factors. -/
def tensorComm (M N : X.Modules) : tensorObj M N ≅ tensorObj N M :=
  (sheafify X).mapIso (β_ M.val N.val)

/-- The explicit sheaf tensor swap is natural in both variables. -/
lemma tensorComm_naturality {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap f g ≫ (tensorComm M' N').hom =
      (tensorComm M N).hom ≫ tensorMap g f := by
  change (sheafify X).map (f.val ⊗ₘ g.val) ≫ (sheafify X).map (β_ M'.val N'.val).hom =
    (sheafify X).map (β_ M.val N.val).hom ≫ (sheafify X).map (g.val ⊗ₘ f.val)
  erw [← Functor.map_comp, ← Functor.map_comp, braiding_naturality]

/-- The left unit isomorphism for the sheafified tensor. -/
def tensorLeftUnitor (M : X.Modules) : tensorObj (structureSheaf X) M ≅ M :=
  (sheafify X).mapIso (λ_ M.val) ≪≫ (sheafifyForgetIso X).app M

/-- The right unit isomorphism for the sheafified tensor. -/
def tensorRightUnitor (M : X.Modules) : tensorObj M (structureSheaf X) ≅ M :=
  (sheafify X).mapIso (ρ_ M.val) ≪≫ (sheafifyForgetIso X).app M

/-- Right-associated nonnegative tensor powers, with zeroth power the structure sheaf. -/
def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => structureSheaf X
  | n + 1 => tensorObj M (tensorPow M n)

/-- The morphism on iterated tensor powers induced by a module morphism. -/
def tensorPowMap {M N : X.Modules} (f : M ⟶ N) :
    (n : ℕ) → (tensorPow M n ⟶ tensorPow N n)
  | 0 => 𝟙 _
  | n + 1 => tensorMap f (tensorPowMap f n)

end Langlands.Scheme.Modules
