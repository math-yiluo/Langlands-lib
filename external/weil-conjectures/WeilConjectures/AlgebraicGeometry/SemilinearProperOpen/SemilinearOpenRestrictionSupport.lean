/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarAdjunctions
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Scalar restriction preserves open support of semilinear systems

## References

* Stacks Project, Modules on Sites, Tags 03DI and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures Opposite

attribute [local irreducible] Functor.leftAdjoint
set_option synthInstance.maxSize 128
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem support_reflect
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    [G.ReflectsIsomorphisms]
    (e : L ⋙ G ≅ F ⋙ l) (d : R ⋙ F ≅ G ⋙ r)
    (hu : ∀ M, F.map (a.unit.app M) ≫ d.hom.app (L.obj M) ≫
      r.map (e.hom.app M) = b.unit.app (F.obj M))
    (N : B) (hN : IsIso (b.counit.app (G.obj N))) : L.essImage N := by
  have hm : (mateEquiv a b e.inv) = d.hom := by
    have hh := mateEquiv_eq_of_unit a b (TwoSquare.mk _ _ _ _ e.inv)
      (TwoSquare.mk _ _ _ _ d.hom) (fun M ↦ ?_)
    · exact hh
    · have ht := congrArg (fun z ↦ z ≫ r.map (e.inv.app M)) (hu M)
      simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at ht
      erw [r.map_id, Category.comp_id] at ht
      exact ht
  have hc := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ e.inv) N
  change l.map ((mateEquiv a b e.inv).app N) ≫ b.counit.app (G.obj N) =
    e.inv.app (R.obj N) ≫ G.map (a.counit.app N) at hc
  rw [hm] at hc
  have : IsIso (b.counit.app (G.obj N)) := hN
  have : IsIso (e.inv.app (R.obj N) ≫ G.map (a.counit.app N)) := by
    rw [← hc]
    infer_instance
  have : IsIso (G.map (a.counit.app N)) := IsIso.of_isIso_comp_left (e.inv.app (R.obj N)) _
  have : IsIso (a.counit.app N) := isIso_of_reflects_iso _ G
  exact a.mem_essImage_of_counit_isIso N

private abbrev Integers := ULift.{u + 1} ℤ

private def integerMap (R : CommRingCat.{u + 1}) : CommRingCat.of Integers ⟶ R :=
  CommRingCat.isInitial.to R

private theorem integerMap_comp (R S : CommRingCat.{u + 1}) (f : R ⟶ S) :
    integerMap R ≫ f = integerMap S := CommRingCat.isInitial.hom_ext _ _

private def integerSheaf_initial (X : Scheme.{u}) :
    IsInitial (ProEtale.StrictTower.coefficients Integers X) :=
  CommRingCat.isInitial.isInitialObj
    (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}) _

private theorem integer_ring_hom_ext (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (f g : (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ProEtale.StrictTower.coefficients Integers X) ⟶
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) : f = g := by
  let F := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat)
  obtain ⟨f', rfl⟩ := F.map_surjective f
  obtain ⟨g', rfl⟩ := F.map_surjective g
  exact congrArg F.map ((integerSheaf_initial X).hom_ext f' g')

attribute [local irreducible] constantSheaf presheafToSheaf SemilinearSections.systemRing

section PushforwardScalars
universe c d v w r m
variable {A : Type c} [Category.{v} A] {B : Type d} [Category.{w} B]
  {J : GrothendieckTopology A} {K : GrothendieckTopology B}
  (F : A ⥤ B) [F.IsContinuous J K]

private def pushforward_then_restrict {R : Sheaf K RingCat.{r}}
    {S T : Sheaf J RingCat.{r}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (b : T ⟶ S) :
    SheafOfModules.pushforward.{m} a ⋙ SheafOfModules.restrictScalars b ≅
      SheafOfModules.pushforward.{m} (F := F) (b ≫ a) := Iso.refl _

private def restrict_then_pushforward {R S : Sheaf K RingCat.{r}}
    {T : Sheaf J RingCat.{r}} (a : R ⟶ S)
    (b : T ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    SheafOfModules.restrictScalars.{m} a ⋙ SheafOfModules.pushforward b ≅
      SheafOfModules.pushforward.{m} (F := F)
        (b ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map a) := Iso.refl _

end PushforwardScalars

attribute [local irreducible] integerMap integerSheaf_initial

section IntegerEvaluation
open ProEtale.VaryingRing SemilinearSections
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
  (X : Scheme.{u}) (n : ℕ)

private def integerEvaluationMap :
    ProEtale.StrictTower.coefficients Integers X ⟶
      ((Prod.sectR n X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology X) (coefficientSequenceTopology (ProEt.topology X))).obj
        (systemRing.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X)
          (coefficientTransition C τ X)) := (integerSheaf_initial X).to _

private def integerEvaluation : Modules C τ X ⥤ ProEtale.StrictTower.Modules Integers X :=
  SheafOfModules.pushforward (F := Prod.sectR n X.ProEt)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat)).map
      (integerEvaluationMap C τ X n))

private def integerEvaluationIso :
    eval C τ X n ⋙ res (ordinaryScalarMap C Integers (fun n ↦ integerMap (C n)) X n) ≅
      integerEvaluation C τ X n := by
  refine pushforward_then_restrict (Prod.sectR n X.ProEt)
    (eqToHom (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology X)
      (coefficients C X) (coefficientTransition C τ X) n).symm)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat)).map
      (ordinaryScalarMap C Integers (fun n ↦ integerMap (C n)) X n)) ≪≫ ?_
  unfold integerEvaluation
  apply SheafOfModules.pushforwardCongr
  apply integer_ring_hom_ext X
    (((Prod.sectR n X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
      (ProEt.topology X) (coefficientSequenceTopology (ProEt.topology X))).obj
      (ProEtale.SemilinearProperOpen.ringSystem C τ X))

variable (D : ℕ → CommRingCat.{u + 1}) (σ : ∀ n, D (n + 1) ⟶ D n)
  (a : ProEtale.SemilinearProperOpen.ringSystem C τ X ⟶
    ProEtale.SemilinearProperOpen.ringSystem D σ X)

private def integerEvaluationScalarIso :
    res a ⋙ integerEvaluation C τ X n ≅ integerEvaluation D σ X n := by
  refine restrict_then_pushforward (Prod.sectR n X.ProEt)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat)).map a)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat)).map
      (integerEvaluationMap C τ X n)) ≪≫ ?_
  unfold integerEvaluation
  apply SheafOfModules.pushforwardCongr
  apply integer_ring_hom_ext X
    (((Prod.sectR n X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
      (ProEt.topology X) (coefficientSequenceTopology (ProEt.topology X))).obj
      (ProEtale.SemilinearProperOpen.ringSystem D σ X))

end IntegerEvaluation

attribute [local semireducible] SemilinearSections.systemRing

section ScalarModels
open ProEtale.VaryingRing SemilinearSections
private theorem scalarModel_reflects
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (X : Scheme.{u}) :
    (SC.rho X).ReflectsIsomorphisms := by
  constructor
  intro M N f hf
  let T := SheafOfModules.forget
    (ring (coefficientSequenceTopology (ProEt.topology X))
      (systemRing.{u + 1, u, u + 1} (ProEt.topology X)
        (coefficients C X) (coefficientTransition C τ X))) ⋙ PresheafOfModules.toPresheaf _
  have hi (V : (ℕ × X.ProEt)ᵒᵖ) : IsIso ((T.map f).app V) := by
    have hl : IsIso ((eval C τ X V.unop.1 ⋙
        res (ordinaryScalarMap C Integers (fun n ↦ integerMap (C n)) X V.unop.1)).map f) :=
      (NatIso.isIso_map_iff (SC.level X V.unop.1) f).mp
        (((CategoryTheory.evaluation ℕᵒᵖ (ProEtale.StrictTower.Modules Integers X)).obj
          (op V.unop.1)).mapIso (@asIso _ _ _ _ ((SC.rho X).map f) hf)).isIso_hom
    exact (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op V.unop.2)).map_isIso
        ((eval C τ X V.unop.1 ⋙
          res (ordinaryScalarMap C Integers (fun n ↦ integerMap (C n)) X V.unop.1)).map f)
  have : IsIso (T.map f) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f T

private def scalarModelLevel
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (X : Scheme.{u}) (n : ℕ) :
    SC.rho X ⋙ (CategoryTheory.evaluation ℕᵒᵖ
      (ProEtale.StrictTower.Modules Integers X)).obj (op n) ≅ integerEvaluation C τ X n :=
  SC.level X n ≪≫ integerEvaluationIso C τ X n

private theorem scalarModelLevel_transition
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (X : Scheme.{u}) (M : Modules C τ X)
    (n : ℕ) (H : X.ProEtᵒᵖ)
    (x : (((SC.rho X).obj M).obj (op (n + 1))).val.obj H) :
    ((scalarModelLevel C τ SC X n).hom.app M).val.app H
        ((((SC.rho X).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H x) =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op
        (((scalarModelLevel C τ SC X (n + 1)).hom.app M).val.app H x) :=
  SC.transitions X M n H x

private def scalarModelComponent
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (D : ℕ → CommRingCat.{u + 1}) (σ : ∀ n, D (n + 1) ⟶ D n)
    (SD : OrdinaryScalarRestriction D σ Integers (fun n ↦ integerMap (D n)))
    (X : Scheme.{u})
    (a : ProEtale.SemilinearProperOpen.ringSystem C τ X ⟶
      ProEtale.SemilinearProperOpen.ringSystem D σ X)
    (M : Modules D σ X) (n : ℕ) :
    ((SC.rho X).obj ((res a).obj M)).obj (op n) ≅ ((SD.rho X).obj M).obj (op n) :=
  (scalarModelLevel C τ SC X n).app ((res a).obj M) ≪≫
    (integerEvaluationScalarIso C τ X n D σ a).app M ≪≫
      ((scalarModelLevel D σ SD X n).app M).symm

private theorem scalarModelComponent_normalization
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (D : ℕ → CommRingCat.{u + 1}) (σ : ∀ n, D (n + 1) ⟶ D n)
    (SD : OrdinaryScalarRestriction D σ Integers (fun n ↦ integerMap (D n)))
    (X : Scheme.{u})
    (a : ProEtale.SemilinearProperOpen.ringSystem C τ X ⟶
      ProEtale.SemilinearProperOpen.ringSystem D σ X)
    (M : Modules D σ X) (n : ℕ)
    (H : X.ProEtᵒᵖ)
    (x : (((SC.rho X).obj ((res a).obj M)).obj (op n)).val.obj H) :
    ((scalarModelLevel D σ SD X n).hom.app M).val.app H
        ((scalarModelComponent C τ SC D σ SD X a M n).hom.val.app H x) =
      ((scalarModelLevel C τ SC X n).hom.app ((res a).obj M)).val.app H x := by
  have h := congrArg (fun f ↦ f.val.app H
    (((scalarModelLevel C τ SC X n).hom.app ((res a).obj M)).val.app H x))
    ((scalarModelLevel D σ SD X n).app M).inv_hom_id
  exact h

private def scalarModelMap
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (D : ℕ → CommRingCat.{u + 1}) (σ : ∀ n, D (n + 1) ⟶ D n)
    (SD : OrdinaryScalarRestriction D σ Integers (fun n ↦ integerMap (D n)))
    (X : Scheme.{u})
    (a : ProEtale.SemilinearProperOpen.ringSystem C τ X ⟶
      ProEtale.SemilinearProperOpen.ringSystem D σ X)
    (M : Modules D σ X) :
    (SC.rho X).obj ((res a).obj M) ⟶ (SD.rho X).obj M :=
  NatTrans.ofOpSequence
    (fun n ↦ (scalarModelComponent C τ SC D σ SD X a M n).hom) (by
      intro n
      ext H x
      let e := (SheafOfModules.evaluation _ H).mapIso
        ((scalarModelLevel D σ SD X n).app M)
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      change ((scalarModelLevel D σ SD X n).hom.app M).val.app H
        ((scalarModelComponent C τ SC D σ SD X a M n).hom.val.app H
          ((((SC.rho X).obj ((res a).obj M)).map
            (homOfLE (Nat.le_succ n)).op).val.app H x)) =
        ((scalarModelLevel D σ SD X n).hom.app M).val.app H
          ((((SD.rho X).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H
            ((scalarModelComponent C τ SC D σ SD X a M (n + 1)).hom.val.app H x))
      rw [scalarModelComponent_normalization]
      have hC := scalarModelLevel_transition C τ SC X ((res a).obj M) n H x
      have hD := scalarModelLevel_transition D σ SD X M n H
        ((scalarModelComponent C τ SC D σ SD X a M (n + 1)).hom.val.app H x)
      have hnorm := scalarModelComponent_normalization C τ SC D σ SD X a M (n + 1) H x
      exact hC.trans ((congrArg
        (fun y : M.val.obj (op (n + 1, H.unop)) ↦
          M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op y)
        hnorm.symm).trans hD.symm))

private def scalarModelIso
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (SC : OrdinaryScalarRestriction C τ Integers (fun n ↦ integerMap (C n)))
    (D : ℕ → CommRingCat.{u + 1}) (σ : ∀ n, D (n + 1) ⟶ D n)
    (SD : OrdinaryScalarRestriction D σ Integers (fun n ↦ integerMap (D n)))
    (X : Scheme.{u})
    (a : ProEtale.SemilinearProperOpen.ringSystem C τ X ⟶
      ProEtale.SemilinearProperOpen.ringSystem D σ X)
    (M : Modules D σ X) :
    (SC.rho X).obj ((res a).obj M) ≅ (SD.rho X).obj M :=
  NatIso.ofComponents (fun n ↦ scalarModelComponent C τ SC D σ SD X a M n.unop)
    (fun f ↦ (scalarModelMap C τ SC D σ SD X a M).naturality f)

end ScalarModels

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

section OrdinaryOpenComparison
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)

private theorem ordinary_coefficient_map_forget_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f) = VaryingRing.ringMap C τ f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map a)
    (eq_of_heq ((coefficientMap_existsUnique C τ f).choose_spec.1 U.unop.1 U.unop.2))

private theorem ordinary_push_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push C τ f = VaryingRing.push C τ f := by
  unfold push VaryingRing.push
  rw [ordinary_coefficient_map_forget_eq]
  rfl

private theorem ordinary_pull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull C τ f = VaryingRing.pull C τ f := by
  unfold pull VaryingRing.pull
  congr 1
  exact ordinary_push_eq C τ f

private theorem ordinary_extension_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : extension C τ j = VaryingRing.extension C τ j := by
  unfold extension VaryingRing.extension
  congr 1
  exact ordinary_pull_eq C τ j

end OrdinaryOpenComparison

/-- Restricting the coefficient action preserves the essential image of ordinary
extension by zero. This specifies no comparison map or adjunction mate. -/
theorem scalarRestriction_ordinaryOpenSupported
    (C D : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) (σ : ∀ n, D (n + 1) ⟶ D n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : ringSystem C τ X ⟶ ringSystem D σ X) (M : Modules D σ U) :
    (extension C τ j).essImage
      ((SemilinearSections.res a).obj ((extension D σ j).obj M)) := by
  rw [ordinary_extension_eq, ordinary_extension_eq]
  obtain ⟨P⟩ := VaryingRing.ordinaryScalarRestriction C τ Integers
    (fun n ↦ integerMap (C n)) (fun n ↦ integerMap_comp _ _ (τ n))
  obtain ⟨Q⟩ := VaryingRing.ordinaryScalarRestriction D σ Integers
    (fun n ↦ integerMap (D n)) (fun n ↦ integerMap_comp _ _ (σ n))
  obtain ⟨GP⟩ := VaryingRing.ordinaryScalarAdjunctions C τ Integers
    (fun n ↦ integerMap (C n)) (fun n ↦ integerMap_comp _ _ (τ n)) P
  obtain ⟨GQ⟩ := VaryingRing.ordinaryScalarAdjunctions D σ Integers
    (fun n ↦ integerMap (D n)) (fun n ↦ integerMap_comp _ _ (σ n)) Q
  have := scalarModel_reflects C τ P X
  let b := VaryingRing.scalarTowerOpenAdj Integers j
  let N := (SemilinearSections.res a).obj ((VaryingRing.extension D σ j).obj M)
  let e : (P.rho X).obj N ≅
      (StrictTower.towerJ Integers j).obj ((Q.rho U).obj M) :=
    scalarModelIso C τ P D σ Q X a ((VaryingRing.extension D σ j).obj M) ≪≫
      (GQ.a j).app M
  have hu : IsIso (b.unit.app ((Q.rho U).obj M)) := by
    change IsIso ((VaryingRing.scalarTowerOpenAdj Integers j).unit.app _)
    rw [← GQ.open_unit j M]
    let eη := (@asIso _ _ _ _ (VaryingRing.moduleJAdj D σ j).unit
      (VaryingRing.moduleJAdj_unit_isIso D σ j)).app M
    exact ((Q.rho U).mapIso eη ≪≫ (GQ.b j).app ((VaryingRing.extension D σ j).obj M) ≪≫
      (StrictTower.towerPullback Integers j).mapIso ((GQ.a j).app M)).isIso_hom
  have hc : IsIso (b.counit.app
      ((StrictTower.towerJ Integers j).obj ((Q.rho U).obj M))) := by
    exact IsIso.of_isIso_fac_left (b.left_triangle_components ((Q.rho U).obj M))
  have hcN : IsIso (b.counit.app ((P.rho X).obj N)) :=
    (NatTrans.isIso_app_iff_of_iso b.counit e).mpr hc
  exact support_reflect (VaryingRing.moduleJAdj C τ j) b (P.rho U) (P.rho X)
    (GP.a j) (GP.b j) (GP.open_unit j) N hcN

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
