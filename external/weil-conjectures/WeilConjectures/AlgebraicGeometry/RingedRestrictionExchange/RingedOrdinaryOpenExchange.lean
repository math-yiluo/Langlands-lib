/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedExchangeChainUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit

/-! # Ordinary ringed exchange along an open immersion

## References

* Stacks Project, section-morphism
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  StrictTowerRingedSquare.exchangeModuleSquare proEtaleRingCompositeCoefficients
  exchangeModuleComposition LocallyRingedSpace.comp PresheafedSpace.comp

private abbrev composeObject {A B : Scheme.{u}} (h : A ⟶ B) [WeaklyEtale h] :=
  ProEtaleOpenRestriction.objectComposition h

private def coprojection {A B : Scheme.{u}} (h : A ⟶ B) [WeaklyEtale h]
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology A) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules B R) (E : A.ProEt)
    (s : M.val.obj (op ((composeObject h).obj E))) :
    ((proEtaleRingModulePullback h R S c).obj M).val.obj (op E) :=
  ((proEtaleRingModulePullback h R S c).obj M).val.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h inferInstance trivial).unit.app E).op
      (((proEtaleRingModuleAdjunction h R S c).unit.app M).val.app
        (op ((composeObject h).obj E)) s)

private theorem coprojection_bijective {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (E : X.ProEt) :
    Function.Bijective (coprojection h R S ch M E) := by
  let G := composeObject h
  let : G.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale h)
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h inferInstance trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let c₀ := ch.symm ≪≫
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).leftAdjointUniq b).app R
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let c : B ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology Y)).obj A :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c₀
  let ψ : A ⟶ ((proEtaleBaseChange h).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X)).obj B :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap h R S ch).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) A.obj =
      ψ.hom ≫ (proEtaleBaseChange h).op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext V
    have hc := Adjunction.unit_leftAdjointUniq_hom_app
      (proEtaleSheafAdjunction h CommRingCat.{u + 1}) b R
    have hv := congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app V)) hc.symm
    change _ = (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app V) ≫
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          (ch.hom.hom.app (op ((proEtaleBaseChange h).obj V.unop))) ≫
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          (ch.inv.hom.app (op ((proEtaleBaseChange h).obj V.unop))) ≫
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).leftAdjointUniq b).hom.app
            R).hom.app (op ((proEtaleBaseChange h).obj V.unop)))
    have hi : (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (ch.hom.hom.app (op ((proEtaleBaseChange h).obj V.unop))) ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (ch.inv.hom.app (op ((proEtaleBaseChange h).obj V.unop))) = 𝟙 _ := by
      rw [← Functor.map_comp]
      exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (z.hom.app (op ((proEtaleBaseChange h).obj V.unop)))) ch.hom_inv_id
    rw [← Category.assoc _ _ ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).leftAdjointUniq b).hom.app
        R).hom.app (op ((proEtaleBaseChange h).obj V.unop)))), hi]
    exact hv
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) B.obj = 𝟙 B.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.hom.app ((proEtaleBaseChange h).op.obj (G.op.obj V)))
      (A.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app V ≫ A.obj.map (𝟙 (G.op.obj V)) = c.hom.hom.app V
    rw [A.obj.map_id]
    exact Category.comp_id (c.hom.hom.app V)
  let d := SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂
  let d' : SheafOfModules.pushforward.{u + 1} c.hom ⊣
      proEtaleRingModuleDirectImage h R S ch :=
    d.ofNatIsoRight (SheafOfModules.pushforwardCongr (by
      simp [ψ, proEtaleRingDirectImageMap]))
  let e := d'.leftAdjointUniq (proEtaleRingModuleAdjunction h R S ch)
  have he : ∀ s, (e.hom.app M).val.app (op E) s = coprojection h R S ch M E s := by
    intro s
    have hx := d'.homEquiv_leftAdjointUniq_hom_app
      (proEtaleRingModuleAdjunction h R S ch) M
    have hy := (d'.homEquiv M _).symm_apply_apply (e.hom.app M)
    rw [show d'.homEquiv M _ (e.hom.app M) =
      (proEtaleRingModuleAdjunction h R S ch).unit.app M from hx] at hy
    have hz := congrArg (fun z ↦ z.val.app (op E) s) hy
    exact hz.symm
  let eE := (SheafOfModules.evaluation B (op E)).mapIso (e.app M)
  have hb := ConcreteCategory.bijective_of_isIso eE.hom
  change Function.Bijective (fun s ↦ (e.hom.app M).val.app (op E) s) at hb
  simpa only [he] using hb

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

private def SquareUnitFormula (r : StrictTowerRingedSquare sq)
    (F : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules X r.RX)
    (P : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
    (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
    (T : proEtaleRingModules Y' r.RY' ⥤ proEtaleRingModules X' r.RX')
    (aF : F ⊣ verticalPush r) (aP : P ⊣ proEtaleRingModuleDirectImage g r.RY r.RY' r.cg)
    (aH : H ⊣ proEtaleRingModuleDirectImage g' r.RX r.RX' r.cg')
    (aT : T ⊣ targetPush r) (θ : P ⋙ T ≅ F ⋙ H)
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

private def MateUnitFormula (r : StrictTowerRingedSquare sq)
    (P : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
    (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
    (aP : P ⊣ proEtaleRingModuleDirectImage g r.RY r.RY' r.cg)
    (aH : H ⊣ proEtaleRingModuleDirectImage g' r.RX r.RX' r.cg')
    (σ : proEtaleBaseChange f ⋙ proEtaleBaseChange g' ≅
      proEtaleBaseChange g ⋙ proEtaleBaseChange f')
    (m₀ : verticalPush r ⋙ P ⟶ H ⋙ targetPush r)
    : Prop := ∀ (M : proEtaleRingModules X r.RX) (V : Y.ProEt)
    (s : M.val.obj (op ((proEtaleBaseChange f).obj V))),
    (m₀.app M).val.app
      (op ((proEtaleBaseChange g).obj V))
      ((aP.unit.app ((verticalPush r).obj M)).val.app (op V) s) =
    (H.obj M).val.map (σ.inv.app V).op
      ((aH.unit.app M).val.app (op ((proEtaleBaseChange f).obj V)) s)

private theorem square_unit_aux (r : StrictTowerRingedSquare sq)
    (θ : basePull r ⋙ targetPull r ≅ verticalPull r ⋙ upperPull r)
    (hθ : θ.inv =
      (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg').inv ≫
        (eqToIso (congrArg arrowPull r.exchangeCoefficients_eq.symm)).hom ≫
        (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf').hom)
    : SquareUnitFormula r (verticalPull r) (basePull r) (upperPull r) (targetPull r)
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
    (((adjU r).unit.app ((verticalPull r).obj F)).val.app
      (op ((proEtaleBaseChange f).obj V)) (((adjF r).unit.app F).val.app (op V) m))
    (((adjT r).unit.app ((basePull r).obj F)).val.app
      (op ((proEtaleBaseChange g).obj V)) (((adjG r).unit.app F).val.app (op V) m))
    ha hb

private theorem square_unit (r : StrictTowerRingedSquare sq)
    : SquareUnitFormula r (verticalPull r) (basePull r) (upperPull r) (targetPull r)
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

private theorem mate_on_unit (r : StrictTowerRingedSquare sq)
    (F : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules X r.RX)
    (P : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
    (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
    (T : proEtaleRingModules Y' r.RY' ⥤ proEtaleRingModules X' r.RX')
    (aF : F ⊣ verticalPush r) (aP : P ⊣ proEtaleRingModuleDirectImage g r.RY r.RY' r.cg)
    (aH : H ⊣ proEtaleRingModuleDirectImage g' r.RX r.RX' r.cg')
    (aT : T ⊣ targetPush r) (θ : P ⋙ T ≅ F ⋙ H)
    (σ : proEtaleBaseChange f ⋙ proEtaleBaseChange g' ≅
      proEtaleBaseChange g ⋙ proEtaleBaseChange f')
    (hn : SquareUnitFormula r F P H T aF aP aH aT θ σ)
    (m₀ : verticalPush r ⋙ P ⟶ H ⋙ targetPush r)
    (hm₀ : m₀ = (mateEquiv aF aT (TwoSquare.mk _ _ _ _ θ.hom)))
    : MateUnitFormula r P H aP aH σ m₀ := by
  intro M V s
  subst m₀
  let G := verticalPush r
  let N := G.obj M
  let c := σ.app V
  let HM := H.obj M
  let Q := (F ⋙ H).obj N
  let PTN := (P ⋙ T).obj N
  let t : Q.val.obj (op ((proEtaleBaseChange g').obj
      ((proEtaleBaseChange f).obj V))) := ((aH.unit.app
    (F.obj N)).val.app
      (op ((proEtaleBaseChange f).obj V)) ((aF.unit.app N).val.app (op V) s))
  let z : PTN.val.obj (op ((proEtaleBaseChange f').obj
      ((proEtaleBaseChange g).obj V))) :=
    (aT.unit.app (P.obj N)).val.app
    (op ((proEtaleBaseChange g).obj V)) ((aP.unit.app N).val.app (op V) s)
  have hz : (θ.inv.app N).val.app (op ((proEtaleBaseChange g').obj
      ((proEtaleBaseChange f).obj V))) t = PTN.val.map c.hom.op z :=
    hn N V s
  have ha : (θ.hom.app N).val.app (op ((proEtaleBaseChange f').obj
      ((proEtaleBaseChange g).obj V))) z = Q.val.map c.inv.op t := by
    have hs : PTN.val.map c.inv.op (PTN.val.map c.hom.op z) = z := by
      change (PTN.val.presheaf.map c.hom.op ≫ PTN.val.presheaf.map c.inv.op) z = z
      have hi := congrArg (fun a ↦ PTN.val.presheaf.map a) (congrArg Quiver.Hom.op c.inv_hom_id)
      exact congrArg (fun a ↦ a z)
        ((PTN.val.presheaf.map_comp c.hom.op c.inv.op).symm.trans
          (hi.trans (PTN.val.presheaf.map_id _)))
    have hh := (congrArg (fun x ↦ PTN.val.map c.inv.op x) hz).trans hs
    have hm := (PresheafOfModules.naturality_apply
      (θ.inv.app N).val c.inv.op t).trans hh
    calc
      _ = (θ.hom.app N).val.app
          (op ((proEtaleBaseChange f').obj ((proEtaleBaseChange g).obj V)))
          ((θ.inv.app N).val.app
            (op ((proEtaleBaseChange f').obj ((proEtaleBaseChange g).obj V)))
              (Q.val.map c.inv.op t)) :=
        congrArg (fun x ↦ (θ.hom.app N).val.app
          (op ((proEtaleBaseChange f').obj ((proEtaleBaseChange g).obj V))) x) hm.symm
      _ = _ := congrArg (fun a ↦ a.val.app
          (op ((proEtaleBaseChange f').obj ((proEtaleBaseChange g).obj V)))
            (Q.val.map c.inv.op t))
        (θ.inv_hom_id_app N)
  change ((H.map (aF.counit.app M)).val.app
    (op ((proEtaleBaseChange f').obj
      ((proEtaleBaseChange g).obj V))))
        ((θ.hom.app N).val.app _ z) = _
  rw [ha]
  refine (PresheafOfModules.naturality_apply
    (H.map (aF.counit.app M)).val c.inv.op t).trans ?_
  apply congrArg (fun x ↦ HM.val.map c.inv.op x)
  have hg := aH.unit.naturality
    (aF.counit.app M)
  have hge := congrArg (fun a ↦ a.val.app (op ((proEtaleBaseChange f).obj V))
    ((aF.unit.app N).val.app (op V) s)) hg
  dsimp only [t]
  refine hge.symm.trans ?_
  have hf := congrArg (fun a ↦ a.val.app (op V) s)
    (aF.right_triangle_components M)
  change (aF.counit.app M).val.app (op ((proEtaleBaseChange f).obj V))
    ((aF.unit.app _).val.app (op V) s) = s at hf
  exact congrArg (fun x ↦ (aH.unit.app M).val.app
    (op ((proEtaleBaseChange f).obj V)) x) hf

private theorem ordinary_eq_mate (r : StrictTowerRingedSquare sq) :
    ordinary r = (mateEquiv (adjF r) (adjT r)
      (TwoSquare.mk _ _ _ _ r.exchangeModuleSquare.hom)) := rfl

attribute [local irreducible] ordinary

private theorem ordinary_on_unit (r : StrictTowerRingedSquare sq) :
    MateUnitFormula r (basePull r) (upperPull r) (adjG r) (adjU r)
      (siteSquare (sq := sq)) (ordinary r) := by
  exact mate_on_unit r (verticalPull r) (basePull r) (upperPull r) (targetPull r)
    (adjF r) (adjG r) (adjU r) (adjT r) r.exchangeModuleSquare
    (siteSquare (sq := sq)) (square_unit r) (ordinary r) (ordinary_eq_mate r)

private theorem upper_open (sq : ChosenCartesianSquare g' f' f g)
    [IsOpenImmersion g] : IsOpenImmersion g' := by
  rw [← sq.hom_fst]
  infer_instance

private def sectionArrow [WeaklyEtale g] [WeaklyEtale g'] (E : Y'.ProEt) :
    (composeObject g').obj ((proEtaleBaseChange f').obj E) ⟶
      (proEtaleBaseChange f).obj ((composeObject g).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.map E.hom f' (E.hom ≫ g) f
      (𝟙 E.left) g' g (Category.id_comp _).symm sq.w.symm)
    (pullback.lift_snd _ _ _)

private theorem siteSquare_section [WeaklyEtale g] [WeaklyEtale g']
    (E : Y'.ProEt) :
    (proEtaleBaseChange f').map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          inferInstance trivial).unit.app E) ≫
      (siteSquare (sq := sq)).inv.app ((composeObject g).obj E) =
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g'
      inferInstance trivial).unit.app ((proEtaleBaseChange f').obj E) ≫
      (proEtaleBaseChange g').map (sectionArrow (sq := sq) E) := by
  let V := (composeObject g).obj E
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial
  let b := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g' inferInstance trivial
  let K := proEtaleBaseChange f'
  let G := proEtaleBaseChange g'
  apply MorphismProperty.Over.Hom.ext
  change (K.map (a.unit.app E)).left ≫ ((siteSquare (sq := sq)).inv.app V).left =
    (b.unit.app (K.obj E)).left ≫ (G.map (sectionArrow (sq := sq) E)).left
  dsimp only [siteSquare]
  rw [ProEtaleOpenRestriction.pullback_eqToIso sq.w]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  dsimp [a, b, K, G, V, sectionArrow, proEtaleBaseChange,
    MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
    MorphismProperty.Over.isoMk, MorphismProperty.Comma.isoMk,
    MorphismProperty.Comma.homFromCommaOfIsIso, MorphismProperty.Over.pullback,
    composeObject, ProEtaleOpenRestriction.objectComposition, MorphismProperty.Over.map,
    MorphismProperty.Comma.Hom.comp, MorphismProperty.Comma.mapRight,
    MorphismProperty.Over.mk, MorphismProperty.Comma.isoFromComma,
    MorphismProperty.Over.homMk, Comma.isoMk]
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [Category.assoc]
  · simp [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
private def SectionFormula (r : StrictTowerRingedSquare sq)
    (δ : verticalPush r ⋙ basePull r ⟶ upperPull r ⋙ targetPush r)
    [WeaklyEtale g] [WeaklyEtale g'] : Prop := ∀ (M : proEtaleRingModules X r.RX) (E : Y'.ProEt)
    (s : M.val.obj (op ((proEtaleBaseChange f).obj ((composeObject g).obj E)))),
    (δ.app M).val.app (op E)
        (coprojection g r.RY r.RY' r.cg ((verticalPush r).obj M) E s) =
      coprojection g' r.RX r.RX' r.cg' M ((proEtaleBaseChange f').obj E)
        (M.val.map (sectionArrow (sq := sq) E).op s)

private theorem ordinary_section_aux (r : StrictTowerRingedSquare sq)
    (δ : verticalPush r ⋙ basePull r ⟶ upperPull r ⋙ targetPush r)
    (hδ : MateUnitFormula r (basePull r) (upperPull r) (adjG r) (adjU r)
      (siteSquare (sq := sq)) δ)
    [WeaklyEtale g] [WeaklyEtale g'] : SectionFormula r δ := by
  intro M E s
  let V := (composeObject g).obj E
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial
  let b := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g' inferInstance trivial
  let K := proEtaleBaseChange f'
  let G := proEtaleBaseChange g'
  have hk := siteSquare_section (sq := sq) E
  dsimp only [coprojection]
  erw [PresheafOfModules.naturality_apply]
  change ((upperPull r).obj M).val.map (K.map (a.unit.app E)).op
    ((δ.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (((adjG r).unit.app _).val.app (op V) s)) = _
  rw [hδ]
  erw [← PresheafOfModules.map_comp_apply, ← op_comp, hk, op_comp,
    PresheafOfModules.map_comp_apply]
  congr 1
  exact (PresheafOfModules.naturality_apply ((adjU r).unit.app M).val
    (sectionArrow (sq := sq) E).op s).symm

private theorem ordinary_section (r : StrictTowerRingedSquare sq)
    [WeaklyEtale g] [WeaklyEtale g'] : SectionFormula r (ordinary r) := by
  exact ordinary_section_aux r (ordinary r) (ordinary_on_unit r)

private theorem sectionArrow_isIso [WeaklyEtale g] [WeaklyEtale g'] (E : Y'.ProEt) :
    IsIso (sectionArrow (sq := sq) E) := by
  have hi₁ : sq.isoPullback.inv ≫ g' = pullback.fst f g := by
    calc
      _ = sq.isoPullback.inv ≫ (sq.isoPullback.hom ≫ pullback.fst f g) :=
        congrArg (fun k ↦ sq.isoPullback.inv ≫ k) sq.hom_fst.symm
      _ = _ := sq.isoPullback.inv_hom_id_assoc _
  have hi₂ : sq.isoPullback.inv ≫ f' = pullback.snd f g := by
    calc
      _ = sq.isoPullback.inv ≫ (sq.isoPullback.hom ≫ pullback.snd f g) :=
        congrArg (fun k ↦ sq.isoPullback.inv ≫ k) sq.hom_snd.symm
      _ = _ := sq.isoPullback.inv_hom_id_assoc _
  let i : pullback (E.hom ≫ g) f ⟶ pullback E.hom f' :=
    pullback.lift (pullback.fst _ _)
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ E.hom)
        (by simpa only [Category.assoc] using
          (pullback.condition (f := E.hom ≫ g) (g := f)).symm) ≫ sq.isoPullback.inv)
      (by simp [Category.assoc, hi₂])
  let e : pullback E.hom f' ≅ pullback (E.hom ≫ g) f :=
    { hom := (sectionArrow (sq := sq) E).left
      inv := i
      hom_inv_id := by
        apply pullback.hom_ext
        · simp [sectionArrow, i]
        · apply (cancel_mono sq.isoPullback.hom).mp
          apply pullback.hom_ext <;>
            simp [sectionArrow, i, Category.assoc, sq.hom_fst, sq.hom_snd,
              pullback.condition]
      inv_hom_id := by
        apply pullback.hom_ext <;> simp [sectionArrow, i, Category.assoc, hi₁] }
  let e' : (composeObject g').obj ((proEtaleBaseChange f').obj E) ≅
      (proEtaleBaseChange f).obj ((composeObject g).obj E) :=
    MorphismProperty.Over.isoMk (Q := ⊤) e
    (by change (sectionArrow (sq := sq) E).left ≫
          pullback.snd (E.hom ≫ g) f = _
        simp [sectionArrow])
  change IsIso e'.hom
  infer_instance

private theorem ordinary_app_isIso (r : StrictTowerRingedSquare sq)
    (δ : verticalPush r ⋙ basePull r ⟶ upperPull r ⋙ targetPush r)
    [IsOpenImmersion g]
    (hδ : letI : IsOpenImmersion g' := upper_open (sq := sq); SectionFormula r δ)
    (M : proEtaleRingModules X r.RX) :
    IsIso (δ.app M) := by
  have : IsOpenImmersion g' := upper_open (sq := sq)
  change SectionFormula r δ at hδ
  dsimp only [SectionFormula] at hδ
  apply ProEtaleOpenRestriction.moduleMap_isIso_of_bijective
  intro E
  let Z := E.unop
  have : IsIso (sectionArrow (sq := sq) Z) := sectionArrow_isIso (sq := sq) Z
  have hs := ConcreteCategory.bijective_of_isIso
    (M.val.presheaf.map (sectionArrow (sq := sq) Z).op)
  have hu := coprojection_bijective g' r.RX r.RX' r.cg' M
    ((proEtaleBaseChange f').obj Z)
  have hg := coprojection_bijective g r.RY r.RY' r.cg ((verticalPush r).obj M) Z
  have hb : Function.Bijective
      (fun s ↦ (δ.app M).val.app E
        (coprojection g r.RY r.RY' r.cg ((verticalPush r).obj M) Z s)) := by
    change Function.Bijective (fun s ↦ (δ.app M).val.app (op Z)
      (coprojection g r.RY r.RY' r.cg ((verticalPush r).obj M) Z s))
    simp_rw [hδ]
    exact hu.comp hs
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hg.2 x
    obtain ⟨b, rfl⟩ := hg.2 y
    exact congrArg _ (hb.1 hxy)
  · intro y
    obtain ⟨a, ha⟩ := hb.2 y
    exact ⟨_, ha⟩

/-- The ordinary counit mate is invertible when the base change is open. -/
theorem ordinary_open_isIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) [IsOpenImmersion g] :
    IsIso (ordinary r) := by
  have (M : proEtaleRingModules X r.RX) : IsIso ((ordinary r).app M) :=
    ordinary_app_isIso r (ordinary r) (by
      let : IsOpenImmersion g' := upper_open (sq := sq)
      exact ordinary_section r) M
  exact NatIso.isIso_of_isIso_app (ordinary r)

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
