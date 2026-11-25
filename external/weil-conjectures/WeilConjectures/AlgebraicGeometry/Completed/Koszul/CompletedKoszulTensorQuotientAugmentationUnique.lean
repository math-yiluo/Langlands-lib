/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Uniqueness of the finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
(blueprint: new-y2-completed-koszul-tensor-quotient-augmentation-unique).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

-- Fix the coefficient universe for the polymorphic sheafification instances.
private instance augmentationAbSheafify (X : Scheme.{t}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} X

private instance augmentationAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X

private instance augmentationRingSheafify (X : Scheme.{t}) :
    HasSheafify (ProEt.topology X) CommRingCat.{t + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{t, 0} X

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

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
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (E : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N)
    (hm : E.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
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

-- Express the unit-constraint formula through the sheafification unit before
-- specializing it to the completed coefficients.
private theorem constraintTmul_eq
    {C : Type*} [Category* C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) (s : S.obj.obj V) :
    SheafOfModules.scalarExtensionConstraintTmul φ M V x s =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  rfl

-- Carry out the scalar-extension calculation with symbolic coefficient rings.
-- This keeps elaboration from unfolding the concrete inverse-limit coefficient ring.
private theorem scalarExtendedUnit_isIso
    {C : Type*} [Category* C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (E : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    {M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (u : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶ M)
    [IsIso u]
    (hm : E.map u = eqToHom (h _) ≫
      SheafOfModules.changeOfRingsHom φ _ u ≫ eqToHom (h M).symm)
    (v : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⟶ E.obj M)
    (hv : ∀ V : Cᵒᵖ, v.val.app V (1 : S.obj.obj V) =
      (eqToHom (h M).symm).val.app V
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom]
            (u.val.app V (1 : R.obj.obj V))))) : IsIso v := by
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  obtain ⟨c⟩ := SheafOfModules.scalarExtension_constraint_coherence R S φ
  let v' : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⟶
      E.obj M := c.unitIso.inv ≫ eqToHom (h U).symm ≫ E.map u
  have he : v = v' := by
    apply (E.obj M).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro V
    change v.val.app V (1 : S.obj.obj V) =
      (E.map u).val.app V ((eqToHom (h U).symm).val.app V
        (c.unitIso.inv.val.app V (1 : S.obj.obj V)))
    rw [c.unit_inv V (1 : S.obj.obj V)]
    erw [constraintTmul_eq φ U V (1 : R.obj.obj V) (1 : S.obj.obj V)]
    exact (hv V).trans
      (normalizedScalarTensor_map φ E h u hm V (1 : S.obj.obj V) (1 : R.obj.obj V)).symm
  rw [he]
  dsimp only [v']
  infer_instance

attribute [local irreducible] completedAdicRing completedAdicChangeData in
private theorem completedKoszulUnitZero_isIso (r : ℕ) (a : Fin r → A) (n : ℕ) :
    IsIso (completedAdicKoszulUnitZero T d r a n) := by
  let E := (completedAdicScalarExtensionData T d).choose
  let h := (completedAdicScalarExtensionData T d).choose_spec.choose
  let u := koszulSheafUnitZero T A r a n
  let : IsIso u := koszulSheafUnitZero_isIso T A r a n
  apply scalarExtendedUnit_isIso (completedAdicScalar T d) E h u
    ((completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose u)
    (completedAdicKoszulUnitZero T d r a n)
  intro V
  exact (completedAdicKoszulUnitZero_exists T d r a n).exists.choose_spec V

set_option linter.unusedVariables false in
/-- The unit and nonzero-summand formulas determine a strict augmentation uniquely.

Source: Stacks Project, Tags 091N and 099M, the degree-zero augmentation in the
proof of lemma-naive-completion.
(blueprint: new-y2-completed-koszul-tensor-quotient-augmentation-unique).

Proof: compare two candidate natural transformations after each quotient-level
and complex-degree projection. The degree-zero total summand is fixed by the
unit equation, while every other summand is zero by the vanishing equation.
The total summand injections jointly detect each component map; natural
transformation extensionality then gives equality. -/
theorem completedKoszulTensorQuotientAugmentation_unique
    (r : ℕ) (a : Fin r → A)
    (β γ : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (hβ :
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
        completedAdicKoszulTensorUnit T d r a P n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
            completedQuotientTensorUnit T d P n) ∧
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        completedKoszulTensorSummand T d r a P n p q ≫
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
              (β.app P)).app (op n)).f (p + q) = 0))
    (hγ :
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
        completedAdicKoszulTensorUnit T d r a P n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (γ.app P)).app (op n) =
            completedQuotientTensorUnit T d P n) ∧
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        completedKoszulTensorSummand T d r a P n p q ≫
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
              (γ.app P)).app (op n)).f (p + q) = 0)) :
    β = γ := by
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  let : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  let : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro k
  apply NatTrans.ext
  funext N
  let n := N.unop
  have he : ∀ j : ℤ,
      (((β.app P).f j).app (op n)) = (((γ.app P).f j).app (op n)) := by
    intro j
    change (((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (β.app P)).app (op n)).f j) =
      (((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (γ.app P)).app (op n)).f j)
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = j at hpq
    by_cases hq : q = 0
    · subst q
      simp only [add_zero] at hpq
      cases hpq
      have hu := congrArg (fun f ↦ f.f j) ((hβ.1 P n).trans (hγ.1 P n).symm)
      dsimp only [HomologicalComplex.comp_f, completedAdicKoszulTensorUnit,
        completedAdicKoszulTensorUnitF] at hu
      let : IsIso (completedAdicKoszulUnitZero T d r a n) :=
        completedKoszulUnitZero_isIso T d r a n
      apply (cancel_epi ((ρ_ (P.X j)).inv ≫
        (P.X j ◁ completedAdicKoszulUnitZero T d r a n))).1
      simpa only [Category.assoc, add_zero] using hu
    · subst j
      exact (hβ.2 P n p q hq).trans (hγ.2 P n p q hq).symm
  exact he k

end AlgebraicGeometry.Scheme
