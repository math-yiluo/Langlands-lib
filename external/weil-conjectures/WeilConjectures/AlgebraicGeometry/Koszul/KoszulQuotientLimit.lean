/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
/-!
# The augmentation comparison of Koszul and quotient completions
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency true

open CochainComplex CochainComplex.HomComplex

section Cone

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {P Q : CochainComplex C ℤ} (s : P ⟶ P) (t : Q ⟶ Q)
private lemma cocone_ext {A : CochainComplex C ℤ} (s : P ⟶ P)
    (a b : A ⟶ mappingCocone s)
    (h₁ : a ≫ mappingCocone.fst s = b ≫ mappingCocone.fst s)
    (h₂ : ∀ p, a.f p ≫ (mappingCocone.snd s).v p (p + -1) rfl =
      b.f p ≫ (mappingCocone.snd s).v p (p + -1) rfl) : a = b := by
  ext p
  have h₁' := congrArg (fun f ↦ f.f p) h₁
  dsimp only [HomologicalComplex.comp_f] at h₁'
  calc
    a.f p = a.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = a.f p ≫ ((mappingCocone.fst s).f p ≫ (mappingCocone.inl s).v p p
          (add_zero p) + (mappingCocone.snd s).v p (p + -1) rfl ≫
            (mappingCocone.inr s).1.v (p + -1) p (by omega)) := by
      rw [mappingCocone.id_X]
    _ = b.f p ≫ ((mappingCocone.fst s).f p ≫ (mappingCocone.inl s).v p p
          (add_zero p) + (mappingCocone.snd s).v p (p + -1) rfl ≫
            (mappingCocone.inr s).1.v (p + -1) p (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, h₁', h₂]
    _ = b.f p := by rw [mappingCocone.id_X, Category.comp_id]

end Cone

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false

private lemma koszulConstantOne_isIso (X : Scheme.{t}) (Λ : Type t) [CommRing Λ] :
    IsIso (koszulConstantOne X Λ) := by
  let := (koszulConstantUnit_local X Λ).1
  let := (koszulConstantUnit_local X Λ).2
  let R := adicModuleRing X Λ
  let α := koszulConstantUnit X Λ
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let U : SheafOfModules.{t + 1} R := SheafOfModules.unit R
  let V := (PresheafOfModules.restrictScalars α).obj U.val
  let s : V.sections := V.sectionsMk (fun A ↦ (1 : R.obj.obj A)) (by
    intro A B h
    change R.obj.map h 1 = 1
    exact map_one _)
  let a : P ⟶ V := V.unitHomEquiv.symm s
  let b : (koszulConstantFunctor X Λ).obj
      (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ)) ⟶ U :=
    (PresheafOfModules.sheafificationHomEquiv.{t + 1} α).symm a
  have hb (A : X.ProEtᵒᵖ) :
      b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A
        (1 : ULift.{t + 1} Λ)) = (1 : R.obj.obj A) := by
    have h :=
      (PresheafOfModules.sheafificationHomEquiv.{t + 1} α (P := P) (F := U)).apply_symm_apply a
    have h' := congrArg (fun z ↦ (z.app A) (1 : ULift.{t + 1} Λ)) h
    change b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A
      (1 : ULift.{t + 1} Λ)) = a.app A (1 : ULift.{t + 1} Λ) at h'
    have ha := congrArg (fun z ↦ z.val A) (V.unitHomEquiv.apply_symm_apply s)
    change a.app A (1 : ULift.{t + 1} Λ) = (1 : R.obj.obj A) at ha
    exact h'.trans ha
  have hu (A : X.ProEtᵒᵖ) :
      (koszulConstantOne X Λ).val.app A (1 : R.obj.obj A) =
        (toSheafify (ProEt.topology X) P.presheaf).app A
          (1 : ULift.{t + 1} Λ) :=
    (koszulConstantOne_exists X Λ).exists.choose_spec A
  have hub : koszulConstantOne X Λ ≫ b = 𝟙 U := by
    apply U.unitHomEquiv.injective
    apply Subtype.ext
    funext A
    change b.val.app A ((koszulConstantOne X Λ).val.app A
      (1 : R.obj.obj A)) = (1 : R.obj.obj A)
    rw [hu, hb]
  have hbu : b ≫ koszulConstantOne X Λ = 𝟙 _ := by
    apply (PresheafOfModules.sheafificationHomEquiv.{t + 1} α).injective
    apply PresheafOfModules.hom_ext
    intro A
    apply ModuleCat.hom_ext
    apply (LinearMap.ringLmapEquivSelf (ULift.{t + 1} Λ) ℤ _).injective
    change (koszulConstantOne X Λ).val.app A
      (b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A (1 : ULift.{t + 1} Λ))) =
      (toSheafify (ProEt.topology X) P.presheaf).app A (1 : ULift.{t + 1} Λ)
    rw [hb, hu]
  exact ⟨b, hub, hbu⟩

private lemma koszulSheafUnitZero_isIso (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (r : ℕ) (f : Fin r → Λ) (n : ℕ) :
    IsIso (koszulSheafUnitZero X Λ r f n) := by
  let : IsIso (koszulConstantOne X Λ) := koszulConstantOne_isIso X Λ
  have e : koszulSheafUnitZero X Λ r f n = koszulConstantOne X Λ ≫
      ((koszulConstantFunctor X Λ).mapIso (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
        (Fin r →₀ ULift.{t + 1} Λ)).symm.toModuleIso).hom ≫
      ((koszulConstantFunctor X Λ).mapIso ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (n + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl)).inv := rfl
  rw [e]
  exact IsIso.comp_isIso' this (IsIso.comp_isIso' (Iso.isIso_hom _) (Iso.isIso_inv _))

set_option backward.isDefEq.respectTransparency true

-- The statement elaborates several explicit product and cone constructions.
-- The existing signature names an unused proof binder in its zero-summand clause.
end

end AlgebraicGeometry.Scheme
