import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Action.Basic

/-!
# Functorial coefficient reduction and ideal-adic inverse systems

The terms, transition maps, coefficient maps and limiting cone are constructed
from actual module quotients. No completeness assumption is imposed on the
initial module, and no topological smoothness is asserted for a group action.
-/

noncomputable section

namespace Langlands.Coefficients.AdicSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Reduction of coefficients from `R` to the quotient ring `R / I`. -/
def reduction : ModuleCat.{v} R ⥤ ModuleCat.{v} (R ⧸ I) where
  obj M := ModuleCat.of (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))
  map f := ModuleCat.ofHom (f.hom.reduceModIdeal I)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- The `n`th ideal-power reduction, retaining the original `R`-module structure. -/
def powerReduction (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (M ⧸ (I ^ n • ⊤ : Submodule R M))
  map f := ModuleCat.ofHom ((f.hom.reduceModIdeal (I ^ n)).restrictScalars R)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The natural quotient map to the reduction modulo the `n`th ideal power. -/
def quotientMap (n : ℕ) : 𝟭 (ModuleCat.{v} R) ⟶ powerReduction I n where
  app M := ModuleCat.ofHom (Submodule.mkQ (I ^ n • ⊤))
  naturality _ _ f := by
    ext x
    rfl

/-- The canonical surjective transition from a higher power to a lower power. -/
def transition {m n : ℕ} (h : m ≤ n) : powerReduction I n ⟶ powerReduction I m where
  app M := ModuleCat.ofHom (Submodule.factorPow I M h)
  naturality {M N} f := by
    ext x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

@[simp]
theorem transition_refl (n : ℕ) : transition I (le_refl n) = 𝟙 (powerReduction I n) := by
  ext M x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

@[reassoc (attr := simp)]
theorem transition_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    transition I k ≫ transition I h = transition I (h.trans k) := by
  ext M x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem transition_surjective {m n : ℕ} (h : m ≤ n) (M : ModuleCat.{v} R) :
    Function.Surjective ((transition I h).app M) :=
  Submodule.factor_surjective (Submodule.pow_smul_top_le I M h)

@[reassoc (attr := simp)]
theorem quotientMap_transition {m n : ℕ} (h : m ≤ n) :
    quotientMap I n ≫ transition I h = quotientMap I m := by
  ext M x
  rfl

/-- The inverse system as a functor of the power index. -/
def powers : ℕᵒᵖ ⥤ (ModuleCat.{v} R ⥤ ModuleCat.{v} R) where
  obj n := powerReduction I n.unop
  map f := transition I (leOfHom f.unop)
  map_id _ := transition_refl I _
  map_comp f g := (transition_comp I (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The ideal-adic system, functorially in its input module. -/
def functor : ModuleCat.{v} R ⥤ (ℕᵒᵖ ⥤ ModuleCat.{v} R) :=
  (powers I).flip

/-- The quotient inverse system of an actual coefficient module. -/
abbrev system (M : ModuleCat.{v} R) : ℕᵒᵖ ⥤ ModuleCat.{v} R :=
  (functor I).obj M

/-- The canonical cone from a module to all of its reductions. -/
def quotientCone (M : ModuleCat.{v} R) : Cone (system I M) where
  pt := M
  π :=
    { app := fun n => ModuleCat.ofHom (Submodule.mkQ (I ^ n.unop • ⊤))
      naturality := by
        intro m n f
        ext x
        rfl }

/-- The cone on the existing Mathlib module of compatible quotient sequences. -/
def completionCone (M : ModuleCat.{v} R) : Cone (system I M) where
  pt := ModuleCat.of R (AdicCompletion I M)
  π :=
    { app := fun n => ModuleCat.ofHom (AdicCompletion.eval I M n.unop)
      naturality := by
        intro m n f
        ext x
        exact (x.property (leOfHom f.unop)).symm }

/-- The compatible-sequence module satisfies the actual categorical limit property. -/
def completionConeIsLimit (M : ModuleCat.{v} R) : IsLimit (completionCone I M) where
  lift s := ModuleCat.ofHom (AdicCompletion.lift I
    (fun n => (s.π.app (op n)).hom) (by
      intro m n h
      exact ModuleCat.hom_ext_iff.mp (s.w (homOfLE h).op)))
  fac s n := by
    ext x
    rfl
  uniq s f hf := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    exact CategoryTheory.congr_fun (hf (op n)) x

/-- An action on the coefficient module induces an action on the entire inverse system. -/
def actionFunctor (G : Type w) [Monoid G] :
    Action (ModuleCat.{v} R) G ⥤ Action (ℕᵒᵖ ⥤ ModuleCat.{v} R) G :=
  (functor I).mapAction G

end Langlands.Coefficients.AdicSystem
