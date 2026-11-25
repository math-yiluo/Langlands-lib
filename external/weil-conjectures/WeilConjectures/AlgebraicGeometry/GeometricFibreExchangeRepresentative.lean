/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import all WeilConjectures.AlgebraicGeometry.UnderivedGlobalGermExchange

/-! # Exchange on pointed representatives

Source: Stacks Project, Tags 03Q1 and 0A3U.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma terminal_evaluation_transport {C : Type u} [Category C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T U : C} (hT : IsTerminal T) (hU : IsTerminal U)
    (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).inv.app F ≫
      (Sheaf.ΓNatIsoSheafSections J A hU).hom.app F =
        F.obj.map (hT.from U).op := by
  apply (cancel_epi ((Sheaf.ΓNatIsoSheafSections J A hT).hom.app F)).1
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [eval_eq_res]
  exact (Sheaf.ΓRes_map F (hT.from U).op).symm

set_option maxRecDepth 2048 in
/-- Exchange on a pointed representative is unit restriction to the geometric fibre,
followed by the canonical global-section and terminal-germ maps.
Source: Stacks Project, Tag 03Q1 (3) and Tag 0A3U, the degree-zero compatibility
calculation in step 3 of `lem-weil-pbc-qcqs-geometric-exchange-factorization`.
(blueprint: lem-weil-pbc-exchange-pointed-representative).

Proof: the inverse-image stalk unit-germ identity rewrites the source germ followed
by the inverse stalk comparison as the unit section and its pulled-back germ.
Naturality of germs moves exchange before this germ. The pushforward unit identity
`unit_map_baseChangeMap_app` replaces the unit followed by exchange with the unit for
g' and the pushforward square isomorphism. The marked point gives a section of its
neighbourhood over Spec Ω; the germ relation replaces its germ by restriction to the
terminal object followed by the terminal germ. Expand the square's two pullback
composition isomorphisms. Their composite with this section and the terminal-object
identification is `geometricFibreSectionLift`: the first projection is f' followed
by the marked point, the second is g', and the outer second projection is identity.
The pullback universal property identifies these maps. Applying the sheaf and the
unit yields `geometricFibreSectionRestriction`. Expanding
`lowerStarCompGlobalSectionsIso` cancels the global/terminal-section identifications
and gives exactly the displayed final three factors. This calculation uses only a
commutative square, with no finiteness or invertibility assumption. -/
theorem exchange_pointed_representative
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    (Scheme.pointSmallEtale s).toPresheafFiber V v
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫
      (geometricPointSourceStalkIso Λ s
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).inv ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) =
      geometricFibreSectionRestriction Λ sq F V v ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj := by
  let H := (upperStar (ModuleCat.{u + 1} Λ) g').obj F
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f').obj H
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let TX := Scheme.Etale.mk (𝟙 X')
  let t : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj T :=
    Over.homMk (𝟙 _) (Category.comp_id _)
  let e : f'.Etale.obj T ≅ TX :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
      (Spec (.of Ω))).isTerminalObj f'.Etale).uniqueUpToIso
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X')
  let j := (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber T t P.obj
  let d := (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
        TX Over.mkIdTerminal)).inv.app H ≫
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app H ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
        T Over.mkIdTerminal)).hom.app P ≫ j
  have hterm : j = H.obj.map e.inv.op ≫ d := by
    dsimp [d]
    simp only [lowerStarCompGlobalSectionsIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Category.assoc]
    simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_inv_app,
      Functor.mapIso_inv, Iso.op_hom, Iso.symm_inv]
    have hx := terminal_evaluation_transport X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X') TX Over.mkIdTerminal)
      terminalIsTerminal H
    have hy := terminal_evaluation_transport (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
        T Over.mkIdTerminal) P
    erw [reassoc_of% hx, reassoc_of% hy]
    change j = H.obj.map e.inv.op ≫ H.obj.map _ ≫ H.obj.map _ ≫
      H.obj.map (f'.Etale.map _).op ≫ j
    simp only [← H.obj.map_comp_assoc, ← op_comp]
    have hid : f'.Etale.map (terminalIsTerminal.from T) ≫
        (PreservesTerminal.iso f'.Etale).hom ≫
        ((IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          TX Over.mkIdTerminal).from (⊤_ X'.Etale)) ≫ e.inv = 𝟙 (f'.Etale.obj T) := by
      exact ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
        (Spec (.of Ω))).isTerminalObj f'.Etale).hom_ext _ _
    simp only [Category.assoc, Quiver.Hom.unop_op, hid, op_id, H.obj.map_id, Category.id_comp]
  let Q := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let a := geometricPointSourceStalkIso Λ s Q
  change _ = geometricFibreSectionRestriction Λ sq F V v ≫ d
  have hsrc := sourceStalkIso_germ Λ s Q V v
  rw [← Category.assoc] at hsrc
  have hsrc' := (Iso.eq_comp_inv a).2 hsrc
  rw [← Category.assoc, ← hsrc', Category.assoc]
  rw [show (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map _ =
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  rw [← Category.assoc]
  have hu := unit_map_baseChangeMap_app (ModuleCat.{u + 1} Λ) sq F
  have huV := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op V)
  change _ ≫ _ = _ at huV
  erw [huV]
  let w : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj (s.Etale.obj V) :=
    (pointSmallEtaleFiberEtaleIso s (𝟙 _)).inv.app V
      (by simpa only [Category.id_comp] using v)
  let σ : T ⟶ s.Etale.obj V := MorphismProperty.Over.homMk w.left w.w
  have hσ : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.map σ t = w := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  change ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.app
      (op (f.Etale.obj V)) ≫
    ((squareLowerStarIso (ModuleCat.{u + 1} Λ) sq).hom.app H).hom.app (op V) ≫
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber (s.Etale.obj V) w P.obj = _
  rw [← hσ]
  erw [← GrothendieckTopology.Point.toPresheafFiber_w]
  change _ ≫ _ ≫ P.obj.map σ.op ≫ j = _
  rw [hterm]
  let c₁ := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) g' f
  let c₂ := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) f' s (g' ≫ f) sq.w
  change _ ≫ (H.obj.map (c₁.hom.app V).op ≫ H.obj.map (c₂.inv.app V).op) ≫
    H.obj.map (f'.Etale.map σ).op ≫ H.obj.map e.inv.op ≫ d = _
  simp only [← Functor.map_comp, ← op_comp]
  have hlift : e.inv ≫ f'.Etale.map σ ≫ c₂.inv.app V ≫ c₁.hom.app V =
      geometricFibreSectionLift sq V v := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change e.inv.left ≫ (f'.Etale.map σ).left ≫ (c₂.inv.app V).left ≫
        (c₁.hom.app V).left ≫ pullback.fst (pullback.snd V.hom f) g' =
          (geometricFibreSectionLift sq V v).left ≫
            pullback.fst (pullback.snd V.hom f) g'
      simp only [geometricFibreSectionLift]
      apply pullback.hom_ext
      · simp only [Functor.id_obj, Functor.const_obj_obj, Hom.Etale,
          MorphismProperty.Over.pullback_map_left, Functor.comp_obj,
          MorphismProperty.Over.pullbackComp_inv_app_left,
          MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
          Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          limit.lift_π, PullbackCone.mk_π_app, Category.comp_id,
          pullbackLeftPullbackSndIso_hom_fst, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, c₂, c₁]
        erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, pullback.lift_fst]
        have hw := pointSmallEtaleFiberEtaleIso_inv_app_left_fst
          s (𝟙 (Spec (.of Ω))) V (by simpa only [Category.id_comp] using v)
        change σ.left ≫ pullback.fst V.hom s = v.left at hw
        have he : e.inv.left ≫ pullback.snd (𝟙 (Spec (.of Ω))) f' = 𝟙 X' := e.inv.w
        have hefst : e.inv.left ≫ pullback.fst (𝟙 (Spec (.of Ω))) f' = f' := by
          have h := congrArg (fun q : X' ⟶ X' ↦ q ≫ f') he
          erw [Category.assoc, ← pullback.condition, Category.comp_id] at h
          exact h
        simp only [Category.assoc]
        erw [hw]
        change e.inv.left ≫ pullback.fst (𝟙 (Spec (.of Ω))) f' ≫ v.left = f' ≫ v.left
        rw [← Category.assoc, hefst]
      · simp only [Functor.id_obj, Functor.const_obj_obj, Hom.Etale,
          MorphismProperty.Over.pullback_map_left, Functor.comp_obj,
          MorphismProperty.Over.pullbackComp_inv_app_left,
          MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
          Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
          limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
          pullbackLeftPullbackSndIso_hom_snd_assoc, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, c₂, c₁]
        erw [pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_snd]
        have he : e.inv.left ≫ pullback.snd (𝟙 (Spec (.of Ω))) f' = 𝟙 X' := e.inv.w
        change e.inv.left ≫ pullback.snd (𝟙 (Spec (.of Ω))) f' ≫ g' = g'
        rw [← Category.assoc, he]
        exact Category.id_comp g'
    · exact (e.inv ≫ f'.Etale.map σ ≫ c₂.inv.app V ≫ c₁.hom.app V).w.trans
        (geometricFibreSectionLift sq V v).w.symm
  simp only [← H.obj.map_comp_assoc, ← op_comp, Category.assoc]
  rw [hlift]
  rfl


end AlgebraicGeometry.Etale
