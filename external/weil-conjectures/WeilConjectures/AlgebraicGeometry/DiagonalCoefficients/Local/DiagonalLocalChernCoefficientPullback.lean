/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernPullbackData
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientConePush
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Coefficient cone in the horizontal completed Chern square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau
  Functor.ofOpSequence Functor.ofSequence

private theorem single_tower_eq (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℤ) :
    DerivedCategory.singleFunctor (SpTowerShriek.S l (ULift.{u} (Padic l)) X) n =
      DerivedCategory.singleFunctor (Systems X (Arings l (ULift.{u} (Padic l)) X)) n := by
  rfl
private theorem shift_tower_eq (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℤ) :
    shiftFunctor (DerivedCategory (SpTowerShriek.S l (ULift.{u} (Padic l)) X)) n =
      shiftFunctor (DerivedCategory (Systems X (Arings l (ULift.{u} (Padic l)) X))) n := by
  rfl

private theorem ordinaryRlim_naturality
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) {H K : ℕᵒᵖ ⥤ A} (b : H ⟶ K) :
    (DerivedCategory.singleFunctor A 0).map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).map b) ≫
        diagonalOrdinaryRlim L K =
      diagonalOrdinaryRlim L H ≫
        L.R.map ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map b) := by
  let α : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ DerivedCategory.singleFunctor A 0 ⟶
      DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0 ⋙ L.R :=
    Functor.whiskerLeft lim (DerivedCategory.singleFunctorIsoCompQ A 0).hom ≫
      Functor.whiskerRight
        (HomologicalComplex.singleMapHomologicalComplex
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A) (.up ℤ) 0).inv DerivedCategory.Q ≫
      Functor.whiskerLeft (HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0) L.η ≫
      Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ A) 0).inv L.R
  exact α.naturality b

private theorem traceCone_naturality
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) {H K : ℕᵒᵖ ⥤ A} (c : Cone H) (d : Cone K)
    (a : c.pt ⟶ d.pt) (b : H ⟶ K)
    (hab : c.π ≫ b = (Functor.const ℕᵒᵖ).map a ≫ d.π) :
    (DerivedCategory.singleFunctor A 0).map a ≫ diagonalTraceConeMap L K d =
      diagonalTraceConeMap L H c ≫
        L.R.map ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map b) := by
  have hlift : a ≫ limit.lift K d =
      limit.lift H c ≫ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).map b := by
    apply limit.hom_ext
    intro n
    have h := congrArg (fun t ↦ t.app n) hab
    simp only [Category.assoc, limit.lift_π]
    erw [limMap_π, limit.lift_π_assoc]
    exact h.symm
  unfold diagonalTraceConeMap
  rw [← Category.assoc, ← Functor.map_comp, hlift, Functor.map_comp, Category.assoc,
    ordinaryRlim_naturality]
  simp only [Category.assoc]

private theorem exactSquare_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ P ≅ H ⋙ V) (M : A) :
    (Functor.mapDerivedCategorySquareIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      V.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (H.obj M) =
    P.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (s.hom.app M) := by
  dsimp only [Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U P).inv.app
    ((DerivedCategory.singleFunctor A 0).obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor U P M)]

private theorem scalar_mate_homEquiv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : A ⥤ C) (H : B ⥤ D)
    (s : G ⋙ L' ≅ L ⋙ H) {M : A} {N : B} (m : L.obj M ⟶ N) :
    (adj'.homEquiv (G.obj M) (H.obj N)) (s.hom.app M ≫ H.map m) =
      G.map ((adj.homEquiv M N) m) ≫
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).app N := by
  let β := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom))
  have hn := β.naturality m
  simp only [Functor.comp_map] at hn
  have hu := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom) M
  change G.map (adj.unit.app M) ≫ β.app (L.obj M) =
    adj'.unit.app (G.obj M) ≫ R'.map (s.hom.app M) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% hu]

private theorem horizontal_varying_coefficient_square
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : S ⟶ Y'}
    [DiagonalTraceLocalizations l Y] [DiagonalTraceLocalizations l Y']
    (hX : X ⟶ S) (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (d : LocalChernPullbackData l hX p' p) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let NX := SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)
    let α := (d.geometry.ordinaryAdjunction.homEquiv _ _)
      d.coefficient.iso.hom
    let G := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
    (diagonalForget l S).map
          ((p'.restrictionX.F.map α ≫ d.varyingPush.hom.app NX).app (op n)) ≫
        (lowerStar AddCommGrpCat.{u + 1} hX).map
          (p.coefficientsX.coefficientForget.hom.app (op n)) =
      p'.coefficientsX.coefficientForget.hom.app (op n) ≫
        (sheafCompose (Scheme.ProEt.topology S) G).map
          (Scheme.proEtaleConstantDirectImageMap hX CommRingCat.{u + 1}
            (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) := by
  let E := ULift.{u} (Padic l)
  let NX := SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)
  let NS := SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S)
  let α := (d.geometry.ordinaryAdjunction.homEquiv _ _)
    d.coefficient.iso.hom
  dsimp only
  apply (cancel_epi (p'.coefficientsX.coefficientForget.inv.app (op n))).mp
  apply constant_additive_ext S
    (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (fun x ↦ ⟨(ZMod.cast x.down : ℤ), by
      apply ULift.ext
      change x.down = (ZMod.cast x.down : ℤ) • (1 : ZMod (l ^ (n + 1)))
      simpa only [zsmul_eq_mul, mul_one]
        using (ZMod.intCast_zmod_cast x.down).symm⟩)
  intro U
  let y := (p'.coefficientsX.coefficientForget.inv.app (op n)).hom.app U
    (1 : (Scheme.purTwistFiniteRing S l n).obj.obj U)
  have hy := coefficient_inverse_one l S p'.chernX p'.restrictionX p'.coefficientsX n U
  have hα := additive_transport_apply
    (p'.restrictionX.underlying NS n U)
    (p'.restrictionX.underlying (d.geometry.push.obj NX) n U)
    (AddCommGrpCat.ofHom
      ((((p'.restrictionX.F.map α).app (op n)).hom.app U).hom.toAddMonoidHom))
    (AddCommGrpCat.ofHom ((α.val.app (op (n, U.unop))).hom.toAddMonoidHom))
    (p'.restrictionX.morphisms α n U) y
    (1 : (SpTowerClasses.systemRing l E S).obj.obj (op (n, U.unop))) hy
  have hp := push_sections l E d.base d.geometry n NX U
    ((α.val.app (op (n, U.unop)))
      (1 : (SpTowerClasses.systemRing l E S).obj.obj (op (n, U.unop))))
  have hq := d.coefficient.normalization n U
    (1 : (SpTowerShriek.B l E S n).obj.obj U)
    (1 : (SpTowerClasses.systemRing l E S).obj.obj (op (n, U.unop))) (HEq.rfl)
  have hβ : HEq
      (((d.varyingPush.hom.app NX).app (op n)).hom.app U
        (((p'.restrictionX.F.map α).app (op n)).hom.app U y))
      (1 : (SpTowerClasses.systemRing l E X).obj.obj
        (op (n, ((Scheme.proEtaleBaseChange hX).op.obj U).unop))) := by
    exact (d.varyingPush_sections NX n U _).trans
      (hα.trans (hp.symm.trans (hq.trans (heq_of_eq (map_one _)))))
  have hsource := p.coefficientsX.coefficient_one n
    ((Scheme.proEtaleBaseChange hX).op.obj U) _ hβ
  change (p.coefficientsX.coefficientForget.hom.app (op n)).hom.app
      ((Scheme.proEtaleBaseChange hX).op.obj U)
      (((d.varyingPush.hom.app NX).app (op n)).hom.app U
        (((p'.restrictionX.F.map α).app (op n)).hom.app U y)) =
    ((Scheme.proEtaleConstantDirectImageMap hX CommRingCat.{u + 1}
      (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U)
        ((p'.coefficientsX.coefficientForget.hom.app (op n)).hom.app U y)
  have hS := congrArg (fun q ↦ q.hom.app U
    (1 : (Scheme.purTwistFiniteRing S l n).obj.obj U))
    (p'.coefficientsX.coefficientForget.app (op n)).inv_hom_id
  change (p'.coefficientsX.coefficientForget.hom.app (op n)).hom.app U y =
    (1 : (Scheme.purTwistFiniteRing S l n).obj.obj U) at hS
  rw [hS, map_one]
  exact hsource

private theorem horizontal_coefficient_cone_transposed
    (l : ℕ) [Fact l.Prime] {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') (n : ℕ) :
    let U := SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    let U' := SheafOfModules.unit (Scheme.purTwistRing X' (Scheme.purTwistZlCompletion X' l))
    let N' := SpTowerClasses.coefficient X' (Arings l (ULift.{u} (Padic l)) X')
    let a := (Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))).homEquiv U U' r.completedUnit.hom
    let q := d.geometry.ordinaryAdjunction.homEquiv _ _ d.coefficient.iso.hom
    (diagonalCompletedRestriction l X).map a ≫ d.completedPush.hom.app U' ≫
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).map
        (p'.coefficientsX.coefficientProjection.app (op n)) =
      p.coefficientsX.coefficientProjection.app (op n) ≫
        (p.restrictionX.F.map q ≫ d.varyingPush.hom.app N').app (op n) := by
  dsimp only
  have : (diagonalForget l X).Faithful := by unfold diagonalForget; infer_instance
  apply (diagonalForget l X).map_injective
  apply (cancel_mono ((lowerStar AddCommGrpCat.{u + 1} hX).map
    (p'.coefficientsX.coefficientForget.hom.app (op n)))).mp
  ext U x
  let y := (((diagonalCompletedRestriction l X).map
    ((Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))).homEquiv _ _
        r.completedUnit.hom)).hom.app U) x
  let v := (d.completedPush.hom.app
    (SheafOfModules.unit (Scheme.purTwistRing X' (Scheme.purTwistZlCompletion X' l)))).hom.app U y
  have hp := p'.coefficientsX.coefficient_projection n
    ((Scheme.proEtaleBaseChange hX).op.obj U) v
  have hv : v = (((Scheme.proEtaleSheafAdjunction hX CommRingCat.{u + 1}).homEquiv _ _
      (diagonalCompletedCoefficientMap l hX)).hom.app U) x := by
    exact eq_of_heq ((d.completedPush_sections _ U y).trans
      (heq_of_eq (r.completedUnit_normalization U x)))
  have hβ := congrArg (fun q ↦ q.hom.app U
    ((p.coefficientsX.coefficientProjection.app (op n)).hom.app U x))
      (horizontal_varying_coefficient_square l hX p' p d n)
  change (p'.coefficientsX.coefficientForget.hom.app (op n)).hom.app
      ((Scheme.proEtaleBaseChange hX).op.obj U)
      (((p.restrictionX.F.map
        (d.geometry.ordinaryAdjunction.homEquiv _ _ d.coefficient.iso.hom) ≫
          d.varyingPush.hom.app _).app (op n)).hom.app U
          ((p.coefficientsX.coefficientProjection.app (op n)).hom.app U x)) =
    ((Scheme.proEtaleConstantDirectImageMap hX CommRingCat.{u + 1}
      (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U)
      ((p.coefficientsX.coefficientForget.hom.app (op n)).hom.app U
        ((p.coefficientsX.coefficientProjection.app (op n)).hom.app U x)) at hβ
  rw [p.coefficientsX.coefficient_projection] at hβ
  have hc := congrArg (fun q ↦ q.hom.app U x)
    (completed_projection_square l hX n)
  change (p'.coefficientsX.coefficientForget.hom.app (op n)).hom.app
      ((Scheme.proEtaleBaseChange hX).op.obj U)
      ((p'.coefficientsX.coefficientProjection.app (op n)).hom.app
        ((Scheme.proEtaleBaseChange hX).op.obj U) v) = _
  rw [hp, hv]
  exact hc.trans hβ.symm

private theorem horizontal_coefficient_cone
    (l : ℕ) [Fact l.Prime] {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') :
    let M := SheafOfModules.unit
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    let N := SpTowerClasses.coefficient X (Arings l (ULift.{u} (Padic l)) X)
    (Functor.const ℕᵒᵖ).map (d.completedOrdinary.hom.app M ≫
        (diagonalCompletedRestriction l X').map r.completedUnit.hom) ≫
      p'.coefficientsX.coefficientProjection =
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).mapCone
      (Cone.mk _ p.coefficientsX.coefficientProjection)).π ≫
      d.varyingOrdinary.hom.app N ≫ p'.restrictionX.F.map d.coefficient.iso.hom := by
  dsimp only
  apply NatTrans.ext
  funext n
  let adj := upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX
  have hc := scalar_mate_homEquiv
    (Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))) adj
    (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l X')
    d.completedOrdinary r.completedUnit.hom
  have hv := scalar_mate_homEquiv d.geometry.ordinaryAdjunction
    (adj.whiskerRight ℕᵒᵖ) p.restrictionX.F p'.restrictionX.F
    d.varyingOrdinary d.coefficient.iso.hom
  have hcm := d.completedMate
  have hvm := d.varyingMate
  dsimp only [adj] at hc hv
  rw [hcm] at hc
  rw [hvm] at hv
  have hvn := congrArg (fun q ↦ q.app n) hv
  simp only [Adjunction.homEquiv_unit, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app] at hvn
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ ((d.completedOrdinary.hom.app _ ≫
      (diagonalCompletedRestriction l X').map r.completedUnit.hom) ≫
      p'.coefficientsX.coefficientProjection.app n) =
    adj.homEquiv _ _ (((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).map
      (p.coefficientsX.coefficientProjection.app n) ≫
      (d.varyingOrdinary.hom.app _).app n ≫
      (p'.restrictionX.F.map d.coefficient.iso.hom).app n)
  rw [Adjunction.homEquiv_naturality_right, hc,
    Adjunction.homEquiv_naturality_left]
  rw [show adj.homEquiv _ _ ((d.varyingOrdinary.hom.app _).app n ≫
      (p'.restrictionX.F.map d.coefficient.iso.hom).app n) = _ from hvn]
  simpa only [Category.assoc, NatTrans.comp_app, Adjunction.homEquiv_unit,
    Opposite.op_unop] using
    horizontal_coefficient_cone_transposed l hX p p' eX eX' r d n.unop

-- Normalize the two exact single squares and the full derived-limit cone equation.
private theorem exactConeComparison_transport
    {A B C D E E' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category E']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian E']
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (U : A ⥤ B) (H : A ⥤ C) (U' : C ⥤ D) (P : B ⥤ D)
    (V : E ⥤ ℕᵒᵖ ⥤ B) (G : E ⥤ E') (V' : E' ⥤ ℕᵒᵖ ⥤ D)
    [U.Additive] [H.Additive] [U'.Additive] [P.Additive]
    [V.Additive] [G.Additive] [V'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    (s : U ⋙ P ≅ H ⋙ U')
    (t : V ⋙ (Functor.whiskeringRight ℕᵒᵖ B D).obj P ≅ G ⋙ V')
    (L : DiagonalRlim B) (L' : DiagonalRlim D)
    (β : L.R ⋙ P.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory ⋙ L'.R)
    {M : A} {M' : C} {N : E} {N' : E'}
    (m : H.obj M ⟶ M') (n : G.obj N ⟶ N')
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N)
    (π' : (Functor.const ℕᵒᵖ).obj (U'.obj M') ⟶ V'.obj N')
    (hπ : (P.mapCone (Cone.mk _ π)).π ≫ t.hom.app N ≫ V'.map n =
      (Functor.const ℕᵒᵖ).map (s.hom.app M ≫ U'.map m) ≫ π')
    (hβ : P.mapDerivedCategory.map (diagonalTraceConeMap L (V.obj N) (Cone.mk _ π)) ≫
      β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (V.obj N)) ≫
      L'.R.map ((Functor.mapDerivedCategorySingleFunctor
        ((Functor.whiskeringRight ℕᵒᵖ B D).obj P) 0).hom.app (V.obj N)) =
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      diagonalTraceConeMap L' _ (P.mapCone (Cone.mk _ π))) :
    (Functor.mapDerivedCategorySquareIso s).inv.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      P.mapDerivedCategory.map (exactConeComparison U V L M N π) ≫
      β.app (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor E 0).obj N)) ≫
      L'.R.map ((Functor.mapDerivedCategorySquareIso t).hom.app
        ((DerivedCategory.singleFunctor E 0).obj N)) ≫
      L'.R.map (V'.mapDerivedCategory.map
        ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor E' 0).map n)) =
    U'.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map m) ≫
      exactConeComparison U' V' L' M' N' π' := by
  let W := (Functor.whiskeringRight ℕᵒᵖ B D).obj P
  have hn := (V'.mapDerivedCategorySingleFunctor 0).hom.naturality n
  have hm := (U'.mapDerivedCategorySingleFunctor 0).hom.naturality m
  have hnat := β.naturality ((V.mapDerivedCategorySingleFunctor 0).inv.app N)
  simp only [Functor.comp_map] at hn hm hnat
  have hc := traceCone_naturality L' (P.mapCone (Cone.mk _ π)) (Cone.mk _ π')
    (s.hom.app M ≫ U'.map m) (t.hom.app N ≫ V'.map n) hπ
  have hsource : exactConeComparison U V L M N π =
      (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        diagonalTraceConeMap L (V.obj N) (Cone.mk _ π) ≫
        L.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N) := by
    simp only [exactConeComparison, diagonalTraceConeMap, Category.assoc]
  have htarget : exactConeComparison U' V' L' M' N' π' =
      (U'.mapDerivedCategorySingleFunctor 0).hom.app M' ≫
        diagonalTraceConeMap L' (V'.obj N') (Cone.mk _ π') ≫
        L'.R.map ((V'.mapDerivedCategorySingleFunctor 0).inv.app N') := by
    simp only [exactConeComparison, diagonalTraceConeMap, Category.assoc]
  rw [hsource, htarget]
  apply (cancel_mono (L'.R.map ((V'.mapDerivedCategorySingleFunctor 0).hom.app N'))).mp
  simp only [Functor.map_comp, Category.assoc]
  conv_rhs => simp only [← L'.R.map_comp, Iso.inv_hom_id_app]
  erw [L'.R.map_id, Category.comp_id]
  rw [← L'.R.map_comp, ← L'.R.map_comp, hn]
  rw [← L'.R.map_comp, reassoc_of% (exactSquare_single V W G V' t N)]
  simp only [Functor.map_comp]
  rw [reassoc_of% hnat]
  rw [← L'.R.map_comp_assoc, ← W.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  erw [W.mapDerivedCategory.map_id, L'.R.map_id, Category.id_comp]
  rw [reassoc_of% hβ]
  rw [← L'.R.map_comp, ← (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map_comp,
    ← hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (exactSquare_single U P H U' s M)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hm]

private theorem coefficient_derivedIso_eq
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    {b : SpTowerShriek.Base l (ULift.{u} (Padic l))}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f}
    (q : CoefficientPullback l (ULift.{u} (Padic l)) b f g) :
    (q.derivedIso l (ULift.{u} (Padic l))).hom =
      (g.pull.mapDerivedCategorySingleFunctor 0).hom.app
          (coefficient Y (Arings l (ULift.{u} (Padic l)) Y)) ≫
        (DerivedCategory.singleFunctor (Systems X (Arings l (ULift.{u} (Padic l)) X)) 0).map
          q.iso.hom := by
  rfl

-- Instantiate the exact cone diagram on the normalized completed endpoints.
/-- The coefficient-unit cone is preserved by the normalized whole-tower comparison.

Source: latest blueprint, diagonal coefficient changes (3).
(blueprint: lem-diagonal-local-chern-coefficient-pullback).

Proof: use the ordinary scalar squares and the full derived-limit cone equation in the
pullback data. Normalize the right scalar squares on every section, and use their mate
equations for the left squares.
The coefficient-unit cone projects to the actual quotient of a completed scalar. After
pullback, its projection is the quotient of the pulled scalar because the canonical
completed coefficient map commutes with every finite quotient. The coefficient comparison
sends one to one, so its linearity identifies both entire ordinary cones. Apply the cone
field and the exact single comparison to obtain the displayed unit equation. This also
applies to empty schemes; the coefficient unit and its identity are still the ring unit. -/
theorem diagonalLocalChern_coefficient_pullback (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (_hunit : IsUnit (l : Γ(X, ⊤))) (_hunit' : IsUnit (l : Γ(X', ⊤)))
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') :
      (d.completedSquare l).inv.app (completedUnit l X) ≫
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory.map
          (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX) ≫
        (d.comparison l).app (SpTowerClasses.unit X (Arings l (ULift.{u} (Padic l)) X)) ≫
        p'.LX.R.map (p'.restrictionX.F.mapDerivedCategory.map
          (d.coefficient.derivedIso l (ULift.{u} (Padic l))).hom) =
      (diagonalCompletedUnderlying l X').map
        (diagonalRealizationPullSingle l hX r.completedUnit).hom ≫
        p'.coefficientsX.unitMap l (ULift.{u} (Padic l)) p'.LX := by
  let W := ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj (upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX))
  let := d.geometry.pullAdditive
  let := d.geometry.pullLimits
  let := d.geometry.pullColimits
  let := p.restrictionX.additive
  let := p.restrictionX.limits
  let := p.restrictionX.colimits
  let := p'.restrictionX.additive
  let := p'.restrictionX.limits
  let := p'.restrictionX.colimits
  let : PreservesFiniteLimits W := d.towerLimits
  let : PreservesFiniteColimits W := d.towerColimits
  have hπ := horizontal_coefficient_cone l hX p p' eX eX' r d
  have ht := exactConeComparison_transport
    (E' := Systems X' (Arings l (ULift.{u} (Padic l)) X'))
    (diagonalCompletedRestriction l X) (diagonalRealizationPull l hX)
    (diagonalCompletedRestriction l X') ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX))
    p.restrictionX.F d.geometry.pull p'.restrictionX.F
    d.completedOrdinary d.varyingOrdinary p.LX p'.LX d.limitMate
    r.completedUnit.hom d.coefficient.iso.hom
    p.coefficientsX.coefficientProjection p'.coefficientsX.coefficientProjection
    (by
      simpa only [Functor.mapCone, NatTrans.ext_iff,
        NatTrans.comp_app, Functor.compConstIso, NatIso.ofComponents_hom_app,
        Iso.refl_hom, Functor.whiskerRight_app, Functor.const_map_app,
        Category.id_comp] using hπ.symm)
    (d.cone _ (Cone.mk _ p.coefficientsX.coefficientProjection))
  simpa only [LocalChernPullbackData.completedSquare,
    LocalChernPullbackData.comparison,  NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Coefficients.unitMap,
    diagonalRealizationPullSingle, coefficient_derivedIso_eq, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    diagonalCompletedUnderlying, completedUnit, completedLine, SpTowerClasses.unit,
    SpTowerClasses.line, single_tower_eq] using ht

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
