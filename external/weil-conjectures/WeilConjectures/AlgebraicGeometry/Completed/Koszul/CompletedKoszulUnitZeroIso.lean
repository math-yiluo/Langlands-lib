/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # The degree-zero completed Koszul unit is invertible

Source: Stacks Project, Tag 099M, the finite Koszul construction; Tag 03EK,
scalar extension of module sheaves.
(blueprint: lem-weil-pbc-completed-koszul-unit-zero-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

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
  let : IsIso (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap) := by
    change IsIso (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).symm.toModuleIso.hom
    infer_instance
  dsimp only [koszulSheafUnitZero]
  infer_instance

private theorem normalizedScalarTensor_map
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}] [HasWeakSheafify J AddCommGrpCat.{t + 1}]
    {R S : Sheaf J CommRingCat.{t + 1}} (φ : R ⟶ S)
    (E : SheafOfModules.{t + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{t + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    {M N : SheafOfModules.{t + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.map f).val.app U ((eqToHom (h M).symm).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
      (eqToHom (h N).symm).val.app U
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] (f.val.app U x))) := by
  have he : eqToHom (h M).symm ≫ E.map f =
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm := by
    rw [hm]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have he' := congrArg (fun k ↦ k.val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) he
  refine he'.trans (congrArg (fun z ↦ (eqToHom (h N).symm).val.app U z) ?_)
  let g : SheafOfModules.changeOfRingsPresheaf φ M ⟶
      SheafOfModules.changeOfRingsPresheaf φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
  have hn := congrArg (fun k ↦ k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
    (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map g))
  change (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      (((ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U))
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    (SheafOfModules.changeOfRingsHom φ M f).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) at hn
  erw [ModuleCat.ExtendScalars.map_tmul] at hn
  exact hn.symm

attribute [local irreducible] completedAdicRing in
/-- The specified degree-zero completed Koszul unit is an isomorphism.
Source: Stacks Project, Tag 099M, finite Koszul complexes; Tag 03EK, scalar extension.
(blueprint: lem-weil-pbc-completed-koszul-unit-zero-iso).

Proof: constant module sheafification sends the rank-one module to the unit.
The inverse sends the constant generator one to the unit section one; the
sheafification Hom equivalence and the unit-module/section equivalence prove the
two inverse identities. Exterior degree zero is canonically the rank-one module,
so the uncompleted Koszul unit is invertible. Apply the actual additive scalar
extension functor to this isomorphism and precompose with the inverse of the
scalar-extension unit comparison. The resulting map sends one to the recorded
sheafified tensor of one with the Koszul unit. Uniqueness in
completedAdicKoszulUnitZero_exists identifies it with the specified completed
unit. Thus that unit is a composite of isomorphisms. This works for rank zero,
the zero ring and the empty scheme. -/
theorem completedKoszulUnitZero_isIso
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (n : ℕ) :
    IsIso (completedAdicKoszulUnitZero T d r a n) := by
  let : EssentiallySmall.{t + 1} T.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let R := adicConstantRing T A
  let S := completedAdicCommRing T d
  let E := completedAdicScalarExtension T d
  let Z := SheafOfModules.unit (adicModuleRing T A)
  let D := Classical.choice (SheafOfModules.scalarExtension_constraint_coherence R S
    (completedAdicScalar T d))
  clear_value D
  let h := (completedAdicScalarExtensionData T d).choose_spec.choose
  let e : E.obj Z ≅ SheafOfModules.unit (completedAdicRing T d) :=
    eqToIso (h Z) ≪≫ D.unitIso
  let u := koszulSheafUnitZero T A r a n
  let : IsIso u := koszulSheafUnitZero_isIso T A r a n
  have hv : e.inv ≫ E.map u = completedAdicKoszulUnitZero T d r a n := by
    apply (completedAdicKoszulUnitZero_exists T d r a n).unique
    · intro U
      have he : e.inv.val.app U (1 : S.obj.obj U) =
          completedAdicScalarTensor T d Z U 1
            (1 : (adicModuleRing T A).obj.obj U) := by
        change (eqToHom (h Z).symm).val.app U
          (D.unitIso.inv.val.app U (1 : S.obj.obj U)) = _
        exact congrArg ((eqToHom (h Z).symm).val.app U)
          (D.unit_inv U (1 : S.obj.obj U))
      change (E.map u).val.app U (e.inv.val.app U (1 : S.obj.obj U)) = _
      rw [he]
      exact normalizedScalarTensor_map (completedAdicScalar T d) E h
        (fun g ↦ (completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose g)
        u U 1 (1 : (adicModuleRing T A).obj.obj U)
    · exact (completedAdicKoszulUnitZero_exists T d r a n).exists.choose_spec
  rw [← hv]
  infer_instance

end AlgebraicGeometry.Scheme
