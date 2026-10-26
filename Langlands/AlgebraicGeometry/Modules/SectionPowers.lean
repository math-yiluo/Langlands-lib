import Langlands.AlgebraicGeometry.Modules.TensorSections

/-! # Nonnegative tensor powers of global module-sheaf sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- The actual right-associated tensor power of a global section, with zeroth
power the unit section of the structure module. -/
def sectionPow (M : X.Modules) (s : GlobalSections M) :
    (n : ℕ) → GlobalSections (tensorPow M n)
  | 0 => (1 : Γ(X, ⊤))
  | n + 1 => tensorSection M (tensorPow M n) s (sectionPow M s n)

variable (M : X.Modules) (s : GlobalSections M)

@[simp]
lemma sectionPow_zero :
    sectionPow M s 0 = (1 : Γ(X, ⊤)) := rfl

@[simp]
lemma sectionPow_succ (n : ℕ) :
    sectionPow M s (n + 1) =
      tensorSection M (tensorPow M n) s (sectionPow M s n) := rfl

/-- The zeroth power corresponds to the identity of the actual structure module. -/
@[simp]
lemma sectionHom_sectionPow_zero :
    sectionHom (tensorPow M 0) (sectionPow M s 0) =
      𝟙 (structureModule X) := by
  change sectionHom (structureSheaf X) (1 : Γ(X, ⊤)) = 𝟙 (structureSheaf X)
  apply (structureSheaf X).unitHomEquiv.injective
  change (structureSheaf X).unitHomEquiv
    ((structureSheaf X).unitHomEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change (PresheafOfModules.unit X.ringCatSheaf.obj).map
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (1 : X.ringCatSheaf.obj.obj (.op ⊤)) =
      (1 : X.ringCatSheaf.obj.obj U)
  exact PresheafOfModules.unit_map_one
    (R := X.ringCatSheaf.obj) (homOfLE (show U.unop ≤ ⊤ from le_top)).op

/-- Successor powers correspond to tensoring the two section morphisms. -/
lemma sectionHom_sectionPow_succ (n : ℕ) :
    sectionHom (tensorPow M (n + 1)) (sectionPow M s (n + 1)) =
      (tensorLeftUnitor (structureSheaf X)).inv ≫
        tensorMap (sectionHom M s)
          (sectionHom (tensorPow M n) (sectionPow M s n)) :=
  sectionHom_tensorSection M (tensorPow M n) s (sectionPow M s n)

/-- Taking powers commutes with the actual map on tensor powers. -/
lemma sectionPow_naturality {M N : X.Modules} (f : M ⟶ N)
    (s : GlobalSections M) (n : ℕ) :
    (tensorPowMap f n).app ⊤ (sectionPow M s n) =
      sectionPow N (f.app ⊤ s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (tensorMap f (tensorPowMap f n)).app ⊤
      (tensorSection M (tensorPow M n) s (sectionPow M s n)) =
        tensorSection N (tensorPow N n) (f.app ⊤ s)
          (sectionPow N (f.app ⊤ s) n)
    rw [tensorSection_naturality, ih]

/-- Naturality of powers, expressed as a composite of section morphisms. -/
lemma sectionHom_sectionPow_naturality {M N : X.Modules} (f : M ⟶ N)
    (s : GlobalSections M) (n : ℕ) :
    sectionHom (tensorPow N n) (sectionPow N (f.app ⊤ s) n) =
      sectionHom (tensorPow M n) (sectionPow M s n) ≫ tensorPowMap f n := by
  rw [← sectionPow_naturality f s n, sectionHom_naturality]

end Langlands.SchemeModule
