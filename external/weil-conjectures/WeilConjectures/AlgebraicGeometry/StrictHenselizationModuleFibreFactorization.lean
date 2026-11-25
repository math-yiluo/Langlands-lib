/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiber
import WeilConjectures.AlgebraicGeometry.StrictLocalExchangeCompatibility

/-! # Factoring fibre restrictions through strict henselization sections

Source: Stacks Project, Tags 03Q9, 03Q1 and 04HX.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The compatible marked maps give a ring cocone and hence a map to its spectrum.
The colimit coprojection formula gives the pointed limit-leg equations (Stacks Tag 04HX). -/
private theorem pointedStrictHenselizationLift
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) :
    ∃ t : Spec (.of Ω) ⟶ strictLocalization s,
      t ≫ strictLocalizationToBase s = s ∧
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        t ≫ (strictHenselizationAffineCone s).π.app (op (op j)) ≫
          Spec.map (ΓSpecIso
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
              j).1.left.unop).inv =
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
            j).2.left := by
  classical
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let c : Cocone (strictHenselizationAffineDiagram s) :=
    { pt := Γ(Spec (.of Ω), ⊤)
      ι := { app := fun j ↦ (N.obj j.unop).2.left.appTop
             naturality := by
               intro j k a
               change (Spec.map (N.map a.unop).1.left.unop).appTop ≫
                 (N.obj k.unop).2.left.appTop = (N.obj j.unop).2.left.appTop ≫ 𝟙 _
               rw [Category.comp_id, ← Scheme.Hom.comp_appTop]
               congr 1
               exact congrArg Over.Hom.left (N.map a.unop).2 } }
  let r := (isColimitSmallStrictHenselizationCocone s).desc c
  let t := (Spec (.of Ω)).toSpecΓ ≫ Spec.map r
  have hleg (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      t ≫ (strictHenselizationAffineCone s).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv = (N.obj j).2.left := by
    change ((Spec (.of Ω)).toSpecΓ ≫ Spec.map r) ≫
      Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫ _ = _
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc]
    dsimp only [r]
    rw [(isColimitSmallStrictHenselizationCocone s).fac]
    change (Spec (.of Ω)).toSpecΓ ≫ Spec.map (N.obj j).2.left.appTop ≫ _ = _
    rw [← Scheme.toSpecΓ_naturality_assoc]
    change (N.obj j).2.left ≫ (Spec _).toSpecΓ ≫ _ = _
    rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
    exact Category.comp_id _
  refine ⟨t, ?_, hleg⟩
  let := (strictHenselizationAffineProperties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty
    (C := SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  change t ≫ strictLocalizationToBase s = s
  rw [← strictHenselizationStructuralMap_eq s j]
  rw [← Category.assoc t, ← Category.assoc]
  erw [hleg j]
  exact (N.obj j).2.w

set_option backward.isDefEq.respectTransparency false in
/-- The canonical exchange map has the unit/pointed-lift formula on every germ.
This is the representative calculation from GeometricFibreExchangeGerms (Tag 0EYP),
with no assumed comparison map: the map being evaluated is exchange itself. -/
private theorem fibreExchangeSectionComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ b : (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj
        ((f')_*[ModuleCat.{u + 1} Λ].obj ((g')^*[ModuleCat.{u + 1} Λ].obj F)) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V),
        (pointSmallEtale s).toPresheafFiber V v
            ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj ≫
          (geometricPointSourceStalkIso Λ s ((f)_*[ModuleCat.{u + 1} Λ].obj F)).inv ≫
          (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
            ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) ≫ b.hom =
        geometricFibreSectionRestriction Λ sq.toCommSq F V v := by
  let H : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ) := (g')^*[ModuleCat.{u + 1} Λ].obj F
  let P := (f')_*[ModuleCat.{u + 1} Λ].obj H
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let TX := Scheme.Etale.mk (𝟙 X')
  let t : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj T :=
    Over.homMk (𝟙 _) (Category.comp_id _)
  let e : f'.Etale.obj T ≅ TX :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
      (Spec (.of Ω))).isTerminalObj f'.Etale).uniqueUpToIso
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X')
  let j : P.obj.obj (op T) ⟶
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj P :=
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber T t P.obj
  have : IsIso j := terminalGerm_isIso Λ P
  let b := (asIso j).symm ≪≫ H.obj.mapIso e.op.symm
  refine ⟨b, ?_⟩
  let Q := (f)_*[ModuleCat.{u + 1} Λ].obj F
  let a := geometricPointSourceStalkIso Λ s Q
  intro V v
  change (pointSmallEtale s).toPresheafFiber V v Q.obj ≫
    (a.inv ≫ _ ≫ b.hom) = _
  have hsrc := sourceStalkIso_germ Λ s Q V v
  rw [← Category.assoc] at hsrc
  have hsrc' := (Iso.eq_comp_inv a).2 hsrc
  rw [← Category.assoc, ← hsrc', Category.assoc]
  change _ ≫ _ ≫ _ ≫ b.hom = _
  rw [show (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map _ =
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  rw [← Category.assoc]
  have hu := unit_map_baseChangeMap_app (ModuleCat.{u + 1} Λ) sq.toCommSq F
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
    ((squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app H).hom.app (op V) ≫
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber (s.Etale.obj V) w P.obj ≫
    b.hom = _
  rw [← hσ, ← GrothendieckTopology.Point.toPresheafFiber_w_assoc]
  have hterm : j ≫ b.hom = H.obj.map e.inv.op := by
    simp [b]
  change _ ≫ _ ≫ P.obj.map σ.op ≫ j ≫ b.hom = _
  rw [hterm]
  let c₁ := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) g' f
  let c₂ := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) f' s (g' ≫ f) sq.w
  change _ ≫ (H.obj.map (c₁.hom.app V).op ≫ H.obj.map (c₂.inv.app V).op) ≫
    H.obj.map (f'.Etale.map σ).op ≫ H.obj.map e.inv.op = _
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  have hlift : e.inv ≫ f'.Etale.map σ ≫ c₂.inv.app V ≫ c₁.hom.app V =
      geometricFibreSectionLift sq.toCommSq V v := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change e.inv.left ≫ (f'.Etale.map σ).left ≫ (c₂.inv.app V).left ≫
        (c₁.hom.app V).left ≫ pullback.fst (pullback.snd V.hom f) g' =
          (geometricFibreSectionLift sq.toCommSq V v).left ≫
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
        (geometricFibreSectionLift sq.toCommSq V v).w.symm
  rw [hlift]
  rfl

-- The existing existential witness `ht` is intentionally unused in the statement.
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The module stalk comparison with strict henselization sections, together with
its compatibility with restriction to the given geometric fibre. This assertion
uses no integral or proper hypothesis.

Source: Stacks Project, Tags 03Q9, 03Q1 and 04HX.
(blueprint: lem-sbc-strict-henselization-module-fibre-factorization).

Proof: The marked maps from Spec Omega to all affine pointed neighbourhoods form
a cone. Its unique lift t to their limit is compatible with the structural map.
The closed-fibre theorem for the strict henselization applies to t's image:
its composite with the structural map has image s's point, so that image is the
closed point of the strict henselization.
Pull back X to this limit. Tag 03Q9 identifies its sections with the direct-image
stalk. Apply the module-to-set inverse-image comparison and its unit equation to
the set-valued stalk formula. Since the set comparison and all restriction maps
commute with addition and scalar multiplication, the bijective comparison is a
module isomorphism Theta. Affine pointed neighbourhoods are cofinal, so its
formula extends to every V and v. The pullback lift i has composite g' with the
projection to X. The inverse-image composition isomorphism therefore identifies
i^* q^* F with g'^* F. Global sections followed by the canonical isomorphism to
evaluation at the identity object gives b. Naturality of the units and their
composition equation show that b after restriction along i after Theta takes a
representative z to the unit image restricted along geometricFibreSectionLift:
both lifts have projections f' followed by v and g', so pullback uniqueness makes
them equal. This is the displayed formula, without any injectivity assertion
about restriction along i. All constructions also apply to an empty X. -/
theorem strictHenselizationModuleFibre_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    [IsLocalRing (strictHenselization s)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (t : Spec (.of Ω) ⟶ strictLocalization s)
      (_ : t ≫ strictLocalizationToBase s = s),
      t (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselization s) ∧
      ∃ (i : X' ⟶ pullback f (strictLocalizationToBase s)),
        IsPullback i f' (pullback.snd f (strictLocalizationToBase s)) t ∧
        i ≫ pullback.fst f (strictLocalizationToBase s) = g' ∧
      ∃ Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≅
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
            ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F),
      ∃ b : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj
            ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
        (z : F.obj.obj (op (f.Etale.obj V))),
        b.hom.hom ((globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)).hom
          (Θ.hom.hom ((pointSmallEtale s).toPresheafFiber V v
            ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z))) =
        (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z := by
  classical
  obtain ⟨t, ht, hpoint⟩ := pointedStrictHenselizationLift s
  have hclosed : t (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselization s) := by
    apply (strictHenselizationStructuralMap_fiber_eq_closedPoint
      (A := strictHenselization s) s (Iso.refl _) _).mp
    change (t ≫ strictLocalizationToBase s) (IsLocalRing.closedPoint Ω) = _
    rw [ht]
  let i : X' ⟶ pullback f (strictLocalizationToBase s) :=
    pullback.lift g' (f' ≫ t) (by rw [Category.assoc, ht]; exact sq.w)
  have hiq : i ≫ pullback.fst f (strictLocalizationToBase s) = g' :=
    pullback.lift_fst _ _ _
  have hip : i ≫ pullback.snd f (strictLocalizationToBase s) = f' ≫ t :=
    pullback.lift_snd _ _ _
  have hisq : IsPullback i f' (pullback.snd f (strictLocalizationToBase s)) t := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f (strictLocalizationToBase s))
      (h₂₂ := strictLocalizationToBase s)
    · simpa only [hiq, ht] using sq
    · exact hip
    · exact IsPullback.of_hasPullback _ _
  obtain ⟨Θ, hΘ⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  let e := (upperStarComp (ModuleCat.{u + 1} Λ) i
    (pullback.fst f (strictLocalizationToBase s)) g' hiq.symm).app F
  let G := (g')^*[ModuleCat.{u + 1} Λ].obj F
  let P := (f')_*[ModuleCat.{u + 1} Λ].obj G
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let hT := IsTerminal.isTerminalOfObj
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
    T Over.mkIdTerminal
  let j := (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber T
    (Over.homMk (𝟙 _) (Category.comp_id _)) P.obj
  have : IsIso j := terminalGerm_isIso Λ P
  obtain ⟨b₀, hb₀⟩ := fibreExchangeSectionComparison Λ sq F
  let b := (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).mapIso e.symm ≪≫
    ((lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').app G).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ hT).app P ≪≫ asIso j ≪≫ b₀
  refine ⟨t, ht, hclosed, i, hisq, hiq, Θ, b, ?_⟩
  have hpoint' : ∀ k : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationAffineCone s).π.app (op (op k)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj k).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj k).2.left := by
    intro k
    rw [isoSpec_Spec_inv]
    exact hpoint k
  have hex := strictLocal_exchange_compatibility Λ sq F t hpoint' i hip hiq Θ.hom hΘ
  have hex' :
      Θ.hom ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)
        ≫ b.hom =
      (geometricPointSourceStalkIso Λ s ((f)_*[ModuleCat.{u + 1} Λ].obj F)).inv ≫
        (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
          ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) ≫ b₀.hom := by
    dsimp only at hex
    rw [hex]
    simp [b, e, G, P, T, hT, j, geometricPointSourceStalkIso, Category.assoc]
  intro V v z
  have h := congrArg (fun k ↦ k z)
    ((congrArg (fun k ↦ (pointSmallEtale s).toPresheafFiber V v
      ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj ≫ k) hex').trans (hb₀ V v))
  simpa only [ConcreteCategory.comp_apply, ModuleCat.Hom.hom] using! h

end AlgebraicGeometry.Etale
