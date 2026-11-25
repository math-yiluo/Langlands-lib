/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # The ordinary completed-coefficient direct-image square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem completed_coefficient_square (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (Scheme.purTwistZlCompletionMap S l) ≫ diagonalCompletedCoefficientMap l f =
      Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} ℤ_[l])) ≫ Scheme.purTwistZlCompletionMap X l := by
  apply limit.hom_ext
  intro n
  have hS := (Scheme.purTwistZlCompletionMap_existsUnique S l).exists.choose_spec n.unop
  have hX := (Scheme.purTwistZlCompletionMap_existsUnique X l).exists.choose_spec n.unop
  change Scheme.purTwistZlCompletionMap S l ≫ Scheme.purTwistZlProjection S l n.unop =
    Scheme.purTwistZlReduction S l n.unop at hS
  change Scheme.purTwistZlCompletionMap X l ≫ Scheme.purTwistZlProjection X l n.unop =
    Scheme.purTwistZlReduction X l n.unop at hX
  rw [Category.assoc, diagonalCompletedCoefficientMap, limit.lift_π]
  dsimp only [diagonalCompletedCoefficientComponent]
  rw [← Category.assoc, ← Functor.map_comp, hS, Category.assoc]
  erw [hX]
  exact Scheme.proEtaleConstantInverseImageMap_naturality f _

private theorem constant_ring_unit (T : Scheme.{u}) (A : CommRingCat.{u + 1})
    (U : T.ProEtᵒᵖ) (a : A) :
    (((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A).inv.hom.app U)
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj A))).app U a) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj A)).app U a := by
  let J := Scheme.ProEt.topology T
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let P := (Functor.const T.ProEtᵒᵖ).obj A
  have h : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (F.obj A)) ≫
      (sheafifyMap J (Functor.constComp T.ProEtᵒᵖ A F).inv ≫
        (sheafifyComposeIso J F P).hom) =
      (Functor.constComp T.ProEtᵒᵖ A F).inv ≫ Functor.whiskerRight (toSheafify J P) F := by
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
  exact ConcreteCategory.congr_hom (congr_app h U) a

private theorem completed_constant_sections (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.ProEtᵒᵖ) (a : ULift.{u + 1} ℤ_[l]) :
    (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
        (diagonalCompletedCoefficientMap l f)).hom.app U
      ((Scheme.purTwistZlCompletionMap S l).hom.app U
        ((toSheafify (Scheme.ProEt.topology S)
          ((Functor.const S.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).app U a)) =
      (Scheme.purTwistZlCompletionMap X l).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).app
              ((Scheme.proEtaleBaseChange f).op.obj U) a) := by
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have h := congrArg (adj.homEquiv _ _) (completed_coefficient_square l f)
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] at h
  have hc : (adj.homEquiv _ _)
      (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} ℤ_[l])) :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [hc] at h
  let A := CommRingCat.of (ULift.{u + 1} ℤ_[l])
  let t : (Functor.const S.ProEtᵒᵖ).obj A ⟶
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)).obj :=
    Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A))
  have ht := ((sheafificationAdjunction (Scheme.ProEt.topology S) CommRingCat.{u + 1}).homEquiv
    ((Functor.const S.ProEtᵒᵖ).obj A)
    ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A))).apply_symm_apply t
  have hs := ConcreteCategory.congr_hom (congr_app ht U) a
  have hv := congrArg (fun q ↦ q.hom.app U
    ((toSheafify (Scheme.ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).app U a)) h
  change _ = (Scheme.purTwistZlCompletionMap X l).hom.app
    ((Scheme.proEtaleBaseChange f).op.obj U) _ at hv
  exact hv.trans (congrArg
    ((Scheme.purTwistZlCompletionMap X l).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U)) hs)

private theorem completed_smul (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalCompleted l X)
    (U : S.ProEtᵒᵖ) (a : ULift.{u + 1} ℤ_[l])
    (x : ((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U) :
    @SMul.smul _ _
      (((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U).isModule.toSMul
      a x =
    @SMul.smul _ _
      (((diagonalCompletedRestriction l X ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj M).obj.obj U).isModule.toSMul
      a x := by
  change @SMul.smul _ _
      (M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)).isModule.toSMul
      ((diagonalCompletedCoefficientMap l f).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app _).hom.app U
        ((Scheme.purTwistZlCompletionMap S l).hom.app U
          ((((constantCommuteCompose (Scheme.ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
              (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).inv.hom.app U)
            ((toSheafify (Scheme.ProEt.topology S)
              ((Functor.const S.ProEtᵒᵖ).obj
                (RingCat.of (ULift.{u + 1} ℤ_[l])))).app U a))))) x =
    @SMul.smul _ _
      (M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)).isModule.toSMul
      ((Scheme.purTwistZlCompletionMap X l).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
      ((((constantCommuteCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).inv.hom.app _)
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (RingCat.of (ULift.{u + 1} ℤ_[l])))).app
              ((Scheme.proEtaleBaseChange f).op.obj U) a))) x
  erw [constant_ring_unit S (CommRingCat.of (ULift.{u + 1} ℤ_[l])) U a,
    constant_ring_unit X (CommRingCat.of (ULift.{u + 1} ℤ_[l]))
      ((Scheme.proEtaleBaseChange f).op.obj U) a]
  exact congrArg (fun z ↦ @SMul.smul _ _
    (M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)).isModule.toSMul z x)
    (completed_constant_sections l f U a)

/-- Constant-scalar restriction commutes with completed direct image, by identity on sections.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
completed coefficient comparison before right derivation.
(blueprint: lem-sfb-diagonal-trace-completed-scalar-square).

Proof: the completed coefficient map commutes with constant scalars since its composite
with every finite projection is the constant-sheaf comparison for that quotient.
Take adjoints and evaluate at constant sections. Thus the identity on the section
module over each pulled-back chart is linear. It commutes with chart restrictions
and maps of sheaves, and its inverse is the same identity. -/
@[no_expose] def diagonalTraceCompletedScalarSquare (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    diagonalTracePush l f ⋙ diagonalCompletedRestriction l S ≅
      diagonalCompletedRestriction l X ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f :=
  let F := diagonalTracePush l f ⋙ diagonalCompletedRestriction l S
  let G := diagonalCompletedRestriction l X ⋙
    lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  NatIso.ofComponents (fun M ↦
    { hom := { hom :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (F.obj M).obj.obj U) (Y := (G.obj M).obj.obj U)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a x ↦ completed_smul l f M U a x }
          naturality := by intros; ext x; rfl } }
      inv := { hom :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (G.obj M).obj.obj U) (Y := (F.obj M).obj.obj U)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a x ↦ (completed_smul l f M U a x).symm }
          naturality := by intros; ext x; rfl } }
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (by intros; ext U x; rfl)

/-- The completed scalar square is the identity on sections. -/
theorem diagonalTraceCompletedScalarSquare_hom_app_hom_app (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
    (x : ((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U) :
    HEq (((diagonalTraceCompletedScalarSquare l f).hom.app M).hom.app U x) x :=
  HEq.rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
