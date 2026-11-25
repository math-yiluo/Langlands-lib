/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Normalization of the completed regular Koszul unit

Source: Stacks Project, Tags 03EK and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local instance] koszulConstantFunctor_preservesZero

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

section ScalarUnit
variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)

private def scalarUnitPresheafIso :
    SheafOfModules.changeOfRingsPresheaf φ
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).val :=
  PresheafOfModules.isoMk (fun V ↦ by
    letI := (φ.hom.app V).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid
      (R.obj.obj V) (S.obj.obj V) (S.obj.obj V)).toModuleIso) (by
        intro U V f
        let := (φ.hom.app U).hom.toAlgebra
        let := (φ.hom.app V).hom.toAlgebra
        apply ModuleCat.ExtendScalars.hom_ext
        intro r
        have ht := Classical.choose_spec
          (SheafOfModules.exists_changeOfRingsMap φ
            (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) f)
              (1 : S.obj.obj U) r
        change SheafOfModules.changeOfRingsMap φ
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) f
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] r) = _ at ht
        change (TensorProduct.AlgebraTensorModule.rid
          (R.obj.obj V) (S.obj.obj V) (S.obj.obj V))
            (SheafOfModules.changeOfRingsMap φ
              (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) f
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] r)) = _
        rw [ht]
        change (φ.hom.app V) (R.obj.map f r) * (S.obj.map f (1 : S.obj.obj U)) =
          S.obj.map f ((φ.hom.app U r) * (1 : S.obj.obj U))
        simp only [map_one, mul_one]
        exact NatTrans.naturality_apply φ.hom f r)

private def scalarUnitIso :
    SheafOfModules.changeOfRings φ
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) := by
  let S' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
  let F := PresheafOfModules.sheafification.{w} (R := S') (𝟙 S'.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (R := S') (𝟙 S'.obj)
  let e : (SheafOfModules.unit S').val ≅
      (SheafOfModules.forget S' ⋙ PresheafOfModules.restrictScalars (𝟙 S'.obj)).obj
        (SheafOfModules.unit S') := Iso.refl _
  exact F.mapIso (scalarUnitPresheafIso φ ≪≫ e) ≪≫
    (asIso adj.counit).app (SheafOfModules.unit S')

private lemma scalarUnitIso_section (V : Cᵒᵖ) (s : S.obj.obj V) (r : R.obj.obj V) :
    (scalarUnitIso φ).hom.val.app V
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] r)) = s * (φ.hom.app V r) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (J := J)
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
  let US := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  have h := (adj.homEquiv _ US).apply_symm_apply (scalarUnitPresheafIso φ).hom
  have hh := congrArg (fun f ↦ f.app V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] r)) h
  change (scalarUnitIso φ).hom.val.app V
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] r)) = (φ.hom.app V r) * s at hh
  exact hh.trans (mul_comm (φ.hom.app V r) s)

private lemma scalarUnitIso_inv_one (V : Cᵒᵖ) :
    (scalarUnitIso φ).inv.val.app V (1 : S.obj.obj V) =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom]
            (1 : R.obj.obj V)) := by
  let x := (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] (1 : R.obj.obj V))
  have h : (scalarUnitIso φ).hom.val.app V x = (1 : S.obj.obj V) := by
    simpa only [map_one, mul_one] using scalarUnitIso_section φ V 1 1
  calc
    _ = (scalarUnitIso φ).inv.val.app V ((scalarUnitIso φ).hom.val.app V x) :=
      congrArg (fun y ↦ (scalarUnitIso φ).inv.val.app V y) h.symm
    _ = x := congrArg (fun f ↦ f.val.app V x) (scalarUnitIso φ).hom_inv_id

end ScalarUnit

-- Carry out the scalar-extension calculation with symbolic coefficient rings.
-- This keeps elaboration from unfolding the concrete inverse-limit coefficient ring.
private theorem normalizedScalarUnit_eq
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (E : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    {M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (u : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶ M)
    (hm : E.map u = eqToHom (h _) ≫
      SheafOfModules.changeOfRingsHom φ _ u ≫ eqToHom (h M).symm)
    (v : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⟶ E.obj M)
    (hv : ∀ V : Cᵒᵖ, v.val.app V (1 : S.obj.obj V) =
      (eqToHom (h M).symm).val.app V
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom]
            (u.val.app V (1 : R.obj.obj V))))) :
    v = (scalarUnitIso φ).inv ≫ eqToHom (h _).symm ≫ E.map u := by
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let c := scalarUnitIso φ
  let v' : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⟶
      E.obj M := c.inv ≫ eqToHom (h U).symm ≫ E.map u
  have he : v = v' := by
    apply (E.obj M).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro V
    change v.val.app V (1 : S.obj.obj V) =
      (E.map u).val.app V ((eqToHom (h U).symm).val.app V
        (c.inv.val.app V (1 : S.obj.obj V)))
    rw [scalarUnitIso_inv_one φ V]
    exact (hv V).trans
      (normalizedScalarTensor_map φ E h u hm V (1 : S.obj.obj V) (1 : R.obj.obj V)).symm
  exact he

attribute [local irreducible] completedAdicRing completedAdicChangeData

private lemma map_constant_unit
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (F : C ⥤ D) (G : D ⥤ B) {P : D} {X Y Z : C}
    (u : P ⟶ F.obj X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    G.map (u ≫ F.map f ≫ F.map g) = G.map u ≫ (F ⋙ G).map (f ≫ g) := by
  simp only [Functor.comp_map, Functor.map_comp]

@[irreducible] private def completedRegularUnitIso :
    SheafOfModules.unit (completedAdicRing T d) ≅
      (koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d).obj
        (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)) := by
  let R := adicModuleRing T A
  let G := completedAdicScalarExtension T d
  let hG := (completedAdicScalarExtensionData T d).choose_spec.choose
  let : IsIso (koszulConstantOne T A) := koszulConstantOne_isIso T A
  exact
    (scalarUnitIso (completedAdicScalar T d)).symm ≪≫
      eqToIso (hG (SheafOfModules.unit R)).symm ≪≫
        G.mapIso (asIso (koszulConstantOne T A))

private lemma completedRegularUnitIso_normalization (r : ℕ) (a : Fin r → A) (n : ℕ) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    let z := ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
      (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
        ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ ULift.up (a i ^ (n + 1)))).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv
    completedAdicKoszulUnitZero T d r a n = (completedRegularUnitIso T d).hom ≫ E.map z := by
  let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
  let R := adicModuleRing T A
  let G := completedAdicScalarExtension T d
  let hG := (completedAdicScalarExtensionData T d).choose_spec.choose
  let z := ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
    (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun i ↦ ULift.up (a i ^ (n + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv
  dsimp only
  have hn := normalizedScalarUnit_eq (completedAdicScalar T d) G hG
    (koszulSheafUnitZero T A r a n)
    ((completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose _)
    (completedAdicKoszulUnitZero T d r a n)
    ((completedAdicKoszulUnitZero_exists T d r a n).exists.choose_spec)
  have hc := map_constant_unit (koszulConstantFunctor T A) G
    (koszulConstantOne T A)
    (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
      (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap)
    ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
      (fun i ↦ ULift.up (a i ^ (n + 1)))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv
  exact hn.trans (by
    simpa only [koszulSheafUnitZero, completedRegularUnitIso, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, Functor.mapIso_hom, asIso_hom, Category.assoc, z, E, G] using
      congrArg (fun f ↦ (scalarUnitIso (completedAdicScalar T d)).inv ≫
        eqToHom (hG (SheafOfModules.unit R)).symm ≫ f) hc)

/-- One fixed regular-module isomorphism realizes every normalized degree-zero Koszul unit.

Source: Stacks Project, Modules on Sites, section on tensor products (03EK), and
proetale.tex, proof of lemma-naive-completion (099M).
(blueprint: lem-weil-pbc-completed-koszul-regular-unit-normalization).

Proof: the constant regular-module unit is invertible by the sheafification adjunction:
its inverse sends the sheafified generator 1 back to 1, and both inverse equations are
checked on that generator. For scalar extension of the regular module, use sectionwise
s tensor r mapped to s*phi(r). This tensor isomorphism commutes with restrictions;
sheafification and its counit identify it with the regular module over the new ring.
The inverse sends 1 to the sheafification of 1 tensor 1. Compose that inverse with the
realized constant regular-module unit. For each Koszul level, functoriality of scalar
tensor sends its exterior degree-zero inclusion to the prescribed completed unit on 1.
The unit-module/global-section equivalence proves equality of the maps. This uses no
nonzero-ring, positive-rank, or nonempty-site hypothesis. -/
theorem completedKoszulRegularUnitNormalization
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    ∃ c₀ : SheafOfModules.unit (completedAdicRing T d) ≅
        E.obj (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)),
      ∀ n : ℕ, completedAdicKoszulUnitZero T d r a n = c₀.hom ≫ E.map
        (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
          (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
          ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
            (fun i ↦ ULift.up (a i ^ (n + 1)))).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv) := by
  refine ⟨completedRegularUnitIso T d, ?_⟩
  intro n
  exact completedRegularUnitIso_normalization T d r a n

end AlgebraicGeometry.Scheme
