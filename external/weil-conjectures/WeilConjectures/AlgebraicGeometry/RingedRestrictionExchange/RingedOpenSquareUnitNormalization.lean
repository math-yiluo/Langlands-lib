/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit

/-! # Unit normalization of the actual-ring open square

## References

* Stacks Project, Sites Tag 03CB and Modules on Sites Tag 03D3
* Stacks 09A5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

/-- The canonical chosen fibre-product square. -/
def cartesian {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T) :
    ChosenCartesianSquare (pullback.fst p h) (pullback.snd p h) p h where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

private def ringCompAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    proEtaleSheafInverseImage fg CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} :=
  ((conjugateIsoEquiv (proEtaleSheafAdjunction fg CommRingCat.{u + 1})
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction f CommRingCat.{u + 1}))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g fg hfg).symm) CommRingCat.{u + 1}
      (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

private theorem ringComposite_heq {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) (q : Z ⟶ V) (hq : q = h ≫ k)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    HEq (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
      ((ringCompAt h k q hq).app RV ≪≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso ck ≪≫ ch) := by
  subst q
  rfl

section UnitNormalization

open Opposite

-- The compositor-unit and pasting argument is adapted from the proved private
-- helpers in RingedOrdinaryOpenExchange (the square-unit part of its proof).
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  StrictTowerRingedSquare.exchangeModuleSquare proEtaleRingCompositeCoefficients
  exchangeModuleComposition LocallyRingedSpace.comp PresheafedSpace.comp

set_option backward.defeqAttrib.useBackward true

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

private def siteSquare :
    proEtaleBaseChange f ⋙ proEtaleBaseChange g' ≅
      proEtaleBaseChange g ⋙ proEtaleBaseChange f' :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g' f).symm ≪≫
    eqToIso (congrArg (fun k ↦ proEtaleBaseChange k) sq.w) ≪≫
      MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f' g

private abbrev adjF (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleAdjunction f r.RY r.RX r.cf
private abbrev adjG (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleAdjunction g r.RY r.RY' r.cg
private abbrev adjU (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleAdjunction g' r.RX r.RX' r.cg'
private abbrev adjT (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleAdjunction f' r.RY' r.RX' r.cf'

private theorem exchangeComposition_unit {T T' T'' : Scheme.{u}}
    (h : T' ⟶ T) (g : T'' ⟶ T')
    (RH : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (RI : Sheaf (ProEt.topology T') CommRingCat.{u + 1})
    (RJ : Sheaf (ProEt.topology T'') CommRingCat.{u + 1})
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RH ≅ RI)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RI ≅ RJ)
    (M : proEtaleRingModules T RH) (U : T.ProEt) (x : M.val.obj (op U)) :
    ((exchangeModuleComposition g h RH RI RJ ch cg).hom.app M).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U))
      (((proEtaleRingModuleAdjunction (g ≫ h) RH RJ
        (proEtaleRingCompositeCoefficients g h RH RI RJ ch cg)).unit.app M).val.app
          (op U) x) =
    ((proEtaleRingModulePullback g RI RJ cg).obj
      ((proEtaleRingModulePullback h RH RI ch).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
          (((proEtaleRingModuleAdjunction g RI RJ cg).unit.app
            ((proEtaleRingModulePullback h RH RI ch).obj M)).val.app
              (op ((proEtaleBaseChange h).obj U))
                (((proEtaleRingModuleAdjunction h RH RI ch).unit.app M).val.app (op U) x)) := by
  let adj := (proEtaleRingModuleAdjunction h RH RI ch).comp
    (proEtaleRingModuleAdjunction g RI RJ cg)
  let adjc := proEtaleRingModuleAdjunction (g ≫ h) RH RJ
    (proEtaleRingCompositeCoefficients g h RH RI RJ ch cg)
  let e := exchangeModuleComposition g h RH RI RJ ch cg
  have hn : ExchangeModuleCompositionNormalized g h RH RI RJ ch cg e := by
    unfold e exchangeModuleComposition
    exact (exchangeModuleComposition_existsUnique g h RH RI RJ ch cg).choose_spec.1
  have hu := unit_conjugateEquiv adj adjc e.hom M
  have hu' := congrArg (fun f ↦ f.val.app (op U) x) hu
  have hnval := hn
    ((proEtaleRingModulePullback h RH RI ch ⋙
      proEtaleRingModulePullback g RI RJ cg).obj M) U
    ((adj.unit.app M).val.app (op U) x)
  exact hu'.symm.trans hnval

private abbrev RingedArrow (A B : Scheme.{u})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}) :=
  Σ h : A ⟶ B, (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S

private def arrowPull {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModulePullback z.1 R S z.2

private def arrowBase {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleBaseChange z.1

private def arrowUnit {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S)
    (M : proEtaleRingModules B R) (V : B.ProEt) (m : M.val.obj (op V)) :
    ((arrowPull z).obj M).val.obj (op ((arrowBase z).obj V)) :=
  ((proEtaleRingModuleAdjunction z.1 R S z.2).unit.app M).val.app (op V) m

private theorem coefficient_transport_unit {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : z = w)
    (M : proEtaleRingModules B R) (V : B.ProEt) (m : M.val.obj (op V)) :
    ((eqToIso (congrArg arrowPull e)).hom.app M).val.app (op ((arrowBase z).obj V))
      (arrowUnit z M V m) =
    ((arrowPull w).obj M).val.map ((eqToIso (congrArg arrowBase e)).hom.app V).op
      (arrowUnit w M V m) := by
  cases e
  simp
  rfl

set_option backward.defeqAttrib.useBackward false

private theorem paste_section_units
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {A B Q T : SheafOfModules.{u + 1} R}
    (a : A ≅ Q) (b : B ≅ T) (c : A ≅ B) (d : Q ≅ T)
    (hd : d.hom = a.inv ≫ c.hom ≫ b.hom)
    {U₀ U₁ V₀ V₁ : C} (p : U₀ ≅ U₁) (q : V₀ ≅ V₁) (w : U₀ ≅ V₀)
    (σ : U₁ ≅ V₁) (hσ : p.hom ≫ σ.hom = w.hom ≫ q.hom)
    (x₀ : A.val.obj (op U₀)) (y₀ : B.val.obj (op V₀))
    (x₁ : Q.val.obj (op U₁)) (y₁ : T.val.obj (op V₁))
    (ha : a.hom.val.app (op U₀) x₀ = Q.val.map p.hom.op x₁)
    (hb : b.hom.val.app (op V₀) y₀ = T.val.map q.hom.op y₁)
    (hc : c.hom.val.app (op U₀) x₀ = B.val.map w.hom.op y₀) :
    d.hom.val.app (op U₁) x₁ = T.val.map σ.hom.op y₁ := by
  apply (ConcreteCategory.bijective_of_isIso (T.val.presheaf.map p.hom.op)).1
  change T.val.map p.hom.op _ = T.val.map p.hom.op _
  rw [← PresheafOfModules.naturality_apply, ← ha, hd]
  change b.hom.val.app (op U₀) (c.hom.val.app (op U₀)
    (a.inv.val.app (op U₀) (a.hom.val.app (op U₀) x₀))) = _
  have hi : a.inv.val.app (op U₀) (a.hom.val.app (op U₀) x₀) = x₀ :=
    congrArg (fun z ↦ z.val.app (op U₀) x₀) a.hom_inv_id
  rw [hi, hc, PresheafOfModules.naturality_apply, hb]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp, hσ]

private theorem paste_functor_units
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u + 1}} {A B Q T : C ⥤ SheafOfModules.{u + 1} R}
    (a : A ≅ Q) (b : B ≅ T) (c : A ≅ B) (d : T ≅ Q)
    (hd : d.inv = a.inv ≫ c.hom ≫ b.hom) (N : C)
    {U₀ U₁ V₀ V₁ : D} (p : U₀ ≅ U₁) (q : V₀ ≅ V₁) (w : U₀ ≅ V₀)
    (σ : U₁ ≅ V₁) (hσ : p.hom ≫ σ.hom = w.hom ≫ q.hom)
    (x₀ : (A.obj N).val.obj (op U₀)) (y₀ : (B.obj N).val.obj (op V₀))
    (x₁ : (Q.obj N).val.obj (op U₁)) (y₁ : (T.obj N).val.obj (op V₁))
    (ha : (a.hom.app N).val.app (op U₀) x₀ = (Q.obj N).val.map p.hom.op x₁)
    (hb : (b.hom.app N).val.app (op V₀) y₀ = (T.obj N).val.map q.hom.op y₁)
    (hc : (c.hom.app N).val.app (op U₀) x₀ = (B.obj N).val.map w.hom.op y₀) :
    (d.inv.app N).val.app (op U₁) x₁ = (T.obj N).val.map σ.hom.op y₁ := by
  exact paste_section_units (a.app N) (b.app N) (c.app N) (d.symm.app N)
    (congrArg (fun z ↦ z.app N) hd) p q w σ hσ x₀ y₀ x₁ y₁ ha hb hc

private theorem paste_ringed_units {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : z = w)
    {Q T : proEtaleRingModules B R ⥤ proEtaleRingModules A S}
    (a : arrowPull z ≅ Q) (b : arrowPull w ≅ T) (d : T ≅ Q)
    (hd : d.inv = a.inv ≫ (eqToIso (congrArg arrowPull e)).hom ≫ b.hom)
    (M : proEtaleRingModules B R) (V : B.ProEt) (m : M.val.obj (op V))
    {U₁ V₁ : A.ProEt} (p : (arrowBase z).obj V ≅ U₁)
    (q : (arrowBase w).obj V ≅ V₁) (σ : U₁ ≅ V₁)
    (hs : p.hom ≫ σ.hom =
      ((eqToIso (congrArg arrowBase e)).hom.app V) ≫ q.hom)
    (x₁ : (Q.obj M).val.obj (op U₁)) (y₁ : (T.obj M).val.obj (op V₁))
    (ha : (a.hom.app M).val.app (op ((arrowBase z).obj V)) (arrowUnit z M V m) =
      (Q.obj M).val.map p.hom.op x₁)
    (hb : (b.hom.app M).val.app (op ((arrowBase w).obj V)) (arrowUnit w M V m) =
      (T.obj M).val.map q.hom.op y₁) :
    (d.inv.app M).val.app (op U₁) x₁ = (T.obj M).val.map σ.hom.op y₁ := by
  cases e
  exact paste_functor_units (C := proEtaleRingModules B R) (D := A.ProEt)
    (J := ProEt.topology A)
    (R := (sheafCompose (ProEt.topology A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    (A := arrowPull z) (B := arrowPull z) (Q := Q) (T := T)
    a b (eqToIso (congrArg arrowPull (rfl : z = z))) d hd M p q
    ((eqToIso (congrArg arrowBase (rfl : z = z))).app V) σ hs
    (arrowUnit z M V m) (arrowUnit z M V m) x₁ y₁ ha hb
    (coefficient_transport_unit (rfl : z = z) M V m)

set_option backward.defeqAttrib.useBackward true

private abbrev unitVerticalPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback f r.RY r.RX r.cf
private abbrev unitBasePull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback g r.RY r.RY' r.cg
private abbrev unitUpperPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback g' r.RX r.RX' r.cg'
private abbrev unitTargetPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback f' r.RY' r.RX' r.cf'
private abbrev unitVerticalPush (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleDirectImage f r.RY r.RX r.cf
private abbrev unitTargetPush (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleDirectImage f' r.RY' r.RX' r.cf'

-- Translate this predicate while its isomorphism is a variable; only then insert
-- the selected compositor, whose body is expensive for the kernel to unfold.
private abbrev SquareUnitFormula (r : StrictTowerRingedSquare sq)
    (F : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules X r.RX)
    (P : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
    (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
    (T : proEtaleRingModules Y' r.RY' ⥤ proEtaleRingModules X' r.RX')
    (aF : F ⊣ unitVerticalPush r) (aP : P ⊣ proEtaleRingModuleDirectImage g r.RY r.RY' r.cg)
    (aH : H ⊣ proEtaleRingModuleDirectImage g' r.RX r.RX' r.cg')
    (aT : T ⊣ unitTargetPush r) (θ : P ⋙ T ≅ F ⋙ H)
    (σ : proEtaleBaseChange f ⋙ proEtaleBaseChange g' ≅
      proEtaleBaseChange g ⋙ proEtaleBaseChange f')
    : Prop := ∀ (N : proEtaleRingModules Y r.RY) (V : Y.ProEt) (s : N.val.obj (op V)),
      (θ.inv.app N).val.app
          (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange f).obj V)))
        ((aH.unit.app (F.obj N)).val.app (op ((proEtaleBaseChange f).obj V))
          ((aF.unit.app N).val.app (op V) s)) =
      ((P ⋙ T).obj N).val.map (σ.hom.app V).op
        ((aT.unit.app (P.obj N)).val.app (op ((proEtaleBaseChange g).obj V))
          ((aP.unit.app N).val.app (op V) s))

private theorem square_unit_aux (r : StrictTowerRingedSquare sq)
    (θ : unitBasePull r ⋙ unitTargetPull r ≅ unitVerticalPull r ⋙ unitUpperPull r)
    (hθ : θ.inv =
      (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg').inv ≫
        (eqToIso (congrArg arrowPull r.exchangeCoefficients_eq.symm)).hom ≫
        (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf').hom)
    : SquareUnitFormula r (unitVerticalPull r) (unitBasePull r) (unitUpperPull r) (unitTargetPull r)
      (adjF r) (adjG r) (adjU r) (adjT r) θ (siteSquare (sq := sq)) := by
  intro F V m
  let a := exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg'
  let b := exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf'
  let e := r.exchangeCoefficients_eq.symm
  let c := eqToIso (congrArg arrowPull e)
  let cs : proEtaleBaseChange (g' ≫ f) ≅ proEtaleBaseChange (f' ≫ g) :=
    eqToIso (congrArg arrowBase e)
  let p := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g' f
  let q := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f' g
  have he : θ.inv = a.inv ≫ c.hom ≫ b.hom := hθ
  have ha := exchangeComposition_unit f g' r.RY r.RX r.RX' r.cf r.cg' F V m
  have hb := exchangeComposition_unit g f' r.RY r.RY' r.RX' r.cg r.cf' F V m
  have hs : (p.hom.app V) ≫ (siteSquare (sq := sq)).hom.app V =
      cs.hom.app V ≫ q.hom.app V := by
    dsimp only [siteSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [← Category.assoc, p, Iso.hom_inv_id_app, Category.id_comp]
    rfl
  exact paste_ringed_units e a b θ he F V m (p.app V) (q.app V)
    ((siteSquare (sq := sq)).app V) hs
    (((adjU r).unit.app ((unitVerticalPull r).obj F)).val.app
      (op ((proEtaleBaseChange f).obj V)) (((adjF r).unit.app F).val.app (op V) m))
    (((adjT r).unit.app ((unitBasePull r).obj F)).val.app
      (op ((proEtaleBaseChange g).obj V)) (((adjG r).unit.app F).val.app (op V) m))
    ha hb

private theorem square_unit (r : StrictTowerRingedSquare sq)
    : SquareUnitFormula r (unitVerticalPull r) (unitBasePull r) (unitUpperPull r) (unitTargetPull r)
      (adjF r) (adjG r) (adjU r) (adjT r) r.exchangeModuleSquare (siteSquare (sq := sq)) := by
  have he : r.exchangeModuleSquare.inv =
      (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg').inv ≫
        (eqToIso (congrArg
          (fun z ↦ proEtaleRingModulePullback z.1 r.RY r.RX' z.2)
            r.exchangeCoefficients_eq.symm)).hom ≫
        (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf').hom := by
    simp only [StrictTowerRingedSquare.exchangeModuleSquare, Iso.trans_inv,
      Iso.symm_inv, eqToIso.inv]
    rfl
  exact square_unit_aux r r.exchangeModuleSquare he

-- Keep the isomorphism variable while translating the two unit predicates.
-- This avoids unfolding the selected composite isomorphism during conversion.
end UnitNormalization

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
