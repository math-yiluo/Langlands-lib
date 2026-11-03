import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Flat.Localization

/-! # Relative flatness and flat sections on affine schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- A relatively flat associated sheaf has stalks flat over the affine base ring. -/
lemma flat_stalk_tilde_of_isFlatOver (N : ModuleCat.{u} B)
    (hN : IsFlatOver (Spec.map φ) (tilde N)) (x : PrimeSpectrum B) :
    letI := Module.compHom (stalk (tilde N) x) φ.hom
    Module.Flat A (stalk (tilde N) x) := by
  let : Algebra A ((Spec A).presheaf.stalk ((Spec.map φ) x)) :=
    inferInstanceAs (Algebra A
      ((structurePresheafInCommRingCat A).stalk (PrimeSpectrum.comap φ.hom x)))
  let : IsLocalization (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
      ((Spec A).presheaf.stalk ((Spec.map φ) x)) :=
    inferInstanceAs (IsLocalization (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk (PrimeSpectrum.comap φ.hom x)))
  let : Module A (stalk (tilde N) x) := Module.compHom _ φ.hom
  let := relativeStalkModule (Spec.map φ) (tilde N) x
  have : IsScalarTower A ((Spec A).presheaf.stalk ((Spec.map φ) x))
      (stalk (tilde N) x) := .of_algebraMap_smul (fun a m => by
    change (Spec.map φ).stalkMap x (StructureSheaf.toStalk A _ a) • m =
      (show (Spec B).presheaf.stalk x from StructureSheaf.toStalk B x (φ a)) • m
    exact congrArg (fun t : (Spec B).presheaf.stalk x => t • m)
      (stalkMap_toStalk_apply φ x a))
  have : Module.Flat A ((Spec A).presheaf.stalk ((Spec.map φ) x)) :=
    IsLocalization.flat _ (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
  have : Module.Flat ((Spec A).presheaf.stalk ((Spec.map φ) x))
      (stalk (tilde N) x) := hN x
  exact Module.Flat.trans A ((Spec A).presheaf.stalk ((Spec.map φ) x)) _

/-- Relative stalk flatness of an associated sheaf implies flatness of its defining
module over the actual affine base ring. -/
lemma flat_of_isFlatOver_tilde (N : ModuleCat.{u} B)
    (hN : IsFlatOver (Spec.map φ) (tilde N)) :
    letI := Module.compHom N φ.hom
    Module.Flat A N := by
  let := φ.hom.toAlgebra
  let : Module A N := Module.compHom N φ.hom
  have : IsScalarTower A B N := .of_algebraMap_smul (fun _ _ => rfl)
  let Np (P : Ideal B) [P.IsMaximal] : Type u :=
    stalk (tilde N) (⟨P, inferInstance⟩ : PrimeSpectrum B)
  let mA : ∀ (P : Ideal B) [P.IsMaximal], Module A (Np P) :=
    fun P _ => Module.compHom (Np P) φ.hom
  have hloc (x : PrimeSpectrum B) :
      IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk N x).hom := inferInstance
  exact @Module.flat_of_isLocalized_maximal A B _ _ _ N _ _ _ _ Np
    (fun _ _ => inferInstance)
    mA
    (fun _ _ => inferInstance)
    (fun P _ => by
      let := mA P
      exact .of_algebraMap_smul (fun _ _ => rfl))
    (fun P _ => (tilde.toStalk N ⟨P, inferInstance⟩).hom)
    (fun P _ => hloc ⟨P, inferInstance⟩)
    (fun P _ => flat_stalk_tilde_of_isFlatOver φ N hN ⟨P, inferInstance⟩)

/-- The actual affine section module of a relatively flat quasi-coherent sheaf is
flat over the base ring via the given ring map. -/
lemma flat_moduleSpecΓFunctor_of_isFlatOver (M : (Spec B).Modules)
    [M.IsQuasicoherent] (hM : IsFlatOver (Spec.map φ) M) :
    letI := Module.compHom (moduleSpecΓFunctor.obj M) φ.hom
    Module.Flat A (moduleSpecΓFunctor.obj M) := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact flat_of_isFlatOver_tilde φ (moduleSpecΓFunctor.obj M)
    ((isFlatOver_iff_of_iso (Spec.map φ) (asIso M.fromTildeΓ)).mpr hM)

/-- Modules on the target ring which are flat over the source of the actual ring map. -/
def affineFlatModules : ObjectProperty (ModuleCat.{u} B) := fun N =>
  letI := Module.compHom N φ.hom
  Module.Flat A N

/-- Ordinary affine sections, restricted to relatively flat quasi-coherent sheaves
and with their proved base flatness retained. -/
def flatAffineSectionsFunctor :
    (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf ⊓
      isFlatOver (Spec.map φ)).FullSubcategory ⥤
        (affineFlatModules φ).FullSubcategory :=
  (affineFlatModules φ).lift
    ((SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf ⊓
      isFlatOver (Spec.map φ)).ι ⋙ moduleSpecΓFunctor)
    (fun M => by
      let : M.obj.IsQuasicoherent := M.property.1
      exact flat_moduleSpecΓFunctor_of_isFlatOver φ M.obj M.property.2)

end Langlands.AlgebraicGeometry.Modules
