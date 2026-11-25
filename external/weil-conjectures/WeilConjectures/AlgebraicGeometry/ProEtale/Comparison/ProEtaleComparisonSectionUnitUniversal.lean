/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonDiagonalSection
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative

/-! # The concrete diagonal unit and its unique-extension property

## References

* Stacks Project, Tag 0GLZ, the sectionwise transpose and verification of its two inverse composites
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- Local notation expands the diagonal formula; the public declaration introduces
-- no second copy of the downstream `proEtaleComparisonEtaleSection` definition.
set_option quotPrecheck false in
local notation:max "δ[" X "," F "," U "]" s:max =>
  (by
    let _ : (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).IsContinuous
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback @Etale @Etale le_rfl (U).hom
    exact ((Scheme.etaleSetPullback (U).hom).obj F).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 (U).left) (𝟙 (U).left) (by simp)) (by simp) :
        Scheme.Etale.mk (𝟙 (U).left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).obj U).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ (U).hom) (Type _)
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s)
  : ((Scheme.etaleSetPullback (U).hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (U).left))))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison unit is constructed section by section, by pulling back
along the diagonal and decoding with e.
Naturality in site objects follows from diagonal-section naturality and hres;
naturality in coefficients follows from hfun and naturality of the inverse-image unit. -/
noncomputable def proEtaleComparisonSectionUnit (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
      (A.obj F).obj.obj (op Y) ≃
        ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
      e F Z ((A.obj F).obj.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e F Y s))
    (hfun : ∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
      e F' Y ((A.map ψ).hom.app (op Y) s) =
        ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s)) :
    𝟭 (Sheaf X.smallEtaleTopology (Type (u + 1))) ⟶
      A ⋙ (Scheme.toProEt X).sheafPushforwardContinuous
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) where
  app F := ⟨{
    app U := by
      dsimp only [Functor.id_obj, Functor.comp_obj]
      simpa only [Functor.sheafPushforwardContinuous_obj_obj_obj] using
        (↾fun s ↦ (e F ((Scheme.toProEt X).obj U.unop)).symm
          (δ[X, F, U.unop] s))
    naturality := by
      intro U V g
      apply ConcreteCategory.hom_ext
      intro s
      apply (e F ((Scheme.toProEt X).obj V.unop)).injective
      dsimp
      simp only [Functor.sheafPushforwardContinuous_obj_obj_map]
      erw [hres F ((Scheme.toProEt X).obj U.unop)
        ((Scheme.toProEt X).obj V.unop) ((Scheme.toProEt X).map g.unop)]
      simp only [Equiv.apply_symm_apply]
      exact proEtaleComparisonDiagonalSection_naturality F U.unop V.unop g.unop s
  }⟩
  naturality := by
    intro F F' ψ
    ext U s
    apply (e F' ((Scheme.toProEt X).obj U.unop)).injective
    dsimp
    simp only [Functor.sheafPushforwardContinuous_map_hom_app]
    erw [hfun F F' ψ ((Scheme.toProEt X).obj U.unop)]
    simp only [Equiv.apply_symm_apply]
    let _ : (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom).IsContinuous
        (X.smallGrothendieckTopology @Etale)
        (U.unop.left.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback @Etale @Etale le_rfl U.unop.hom
    have hu := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom)
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale)
          (U.unop.left.smallGrothendieckTopology @Etale)).unit.naturality ψ)) U) s
    have hn := (((Scheme.etaleSetPullback U.unop.hom).map ψ).hom.naturality
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 U.unop.left) (𝟙 U.unop.left) (by simp)) (by simp) :
        Scheme.Etale.mk (𝟙 U.unop.left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom).obj U.unop).op)
    exact (congrArg (((Scheme.etaleSetPullback U.unop.hom).obj F').obj.map _) hu).trans
      (ConcreteCategory.congr_hom hn
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ U.unop.hom) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (U.unop.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app U s)).symm

-- Restrict a pro-étale sheaf to each local étale site, then transpose alpha.
private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private instance b_continuous {S T : Scheme.{u}} (f : T ⟶ S) :
    (b f).IsContinuous (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale) :=
  Scheme.isContinuous_overPullback @Etale @Etale le_rfl f

private noncomputable def push {S T : Scheme.{u}} (f : T ⟶ S) :=
  (b f).sheafPushforwardContinuous (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)

private noncomputable def adj {S T : Scheme.{u}} (f : T ⟶ S) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b f)
    (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)

private def localSite {X : Scheme.{u}} (Y : X.ProEt) : Y.left.Etale ⥤ X.ProEt :=
  Scheme.toProEt Y.left ⋙ MorphismProperty.Over.map ⊤ Y.prop

private instance localSite_continuous {X : Scheme.{u}} (Y : X.ProEt) :
    (localSite Y).IsContinuous Y.left.smallEtaleTopology (Scheme.ProEt.topology X) := by
  let _ : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Y.prop).IsContinuous
      (Scheme.ProEt.topology Y.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap Y.prop
  exact Functor.isContinuous_comp (Scheme.toProEt Y.left)
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Y.prop)
    Y.left.smallEtaleTopology (Scheme.ProEt.topology Y.left) (Scheme.ProEt.topology X)

private def localSheaf {X : Scheme.{u}}
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (Y : X.ProEt) :=
  ((localSite Y).sheafPushforwardContinuous (Type (u + 1))
    Y.left.smallEtaleTopology (Scheme.ProEt.topology X)).obj G

private noncomputable def projection {X : Scheme.{u}} (Y : X.ProEt) (U : X.Etale) :
    (localSite Y).obj ((b Y.hom).obj U) ⟶ (Scheme.toProEt X).obj U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom Y.hom) (by
    change pullback.fst U.hom Y.hom ≫ U.hom = pullback.snd U.hom Y.hom ≫ Y.hom
    exact pullback.condition)

private noncomputable def localAlpha {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) :
    F ⟶ (push Y.hom).obj (localSheaf G Y) := ⟨{
  app U := α.hom.app U ≫ G.obj.map (projection Y U.unop).op
  naturality := by
    intro U V g
    have h := α.hom.naturality g
    dsimp at h ⊢
    rw [reassoc_of% h]
    change α.hom.app U ≫ G.obj.map ((Scheme.toProEt X).map g.unop).op ≫
        G.obj.map (projection Y V.unop).op =
      (α.hom.app U ≫ G.obj.map (projection Y U.unop).op) ≫
        G.obj.map ((localSite Y).map ((b Y.hom).map g.unop)).op
    simp only [Category.assoc]
    rw [← G.obj.map_comp, ← G.obj.map_comp]
    congr 2
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change pullback.fst V.unop.hom Y.hom ≫ g.unop.left =
      ((b Y.hom).map g.unop).left ≫ pullback.fst U.unop.hom Y.hom
    simp [MorphismProperty.Over.pullback_map_left]
}⟩

private noncomputable def localTranspose {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) : (Scheme.etaleSetPullback Y.hom).obj F ⟶ localSheaf G Y :=
  ((adj Y.hom).homEquiv F (localSheaf G Y)).symm (localAlpha F G α Y)

private lemma localTranspose_unit {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) (U : X.Etale) :
    ((adj Y.hom).unit.app F).hom.app (op U) ≫
        (localTranspose F G α Y).hom.app (op ((b Y.hom).obj U)) =
      α.hom.app (op U) ≫ G.obj.map (projection Y U).op := by
  have h := ((adj Y.hom).homEquiv F (localSheaf G Y)).apply_symm_apply
    (localAlpha F G α Y)
  exact congrArg (fun f ↦ f.hom.app (op U)) h

-- The chosen inverse-image composition isomorphism, with its unit equation.
private noncomputable def pullComp {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (k : T ⟶ R) (hk : g ≫ f = k)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    (Scheme.etaleSetPullback g).obj ((Scheme.etaleSetPullback f).obj F) ≅
      (Scheme.etaleSetPullback k).obj F :=
  (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f g).app F ≪≫
    eqToIso (congrArg (fun k ↦ (Scheme.etaleSetPullback k).obj F) hk)

private lemma pullComp_unit {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (k : T ⟶ R) (hk : g ≫ f = k)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    ((adj f).unit.app F).hom.app (op U) ≫
        ((adj g).unit.app ((Scheme.etaleSetPullback f).obj F)).hom.app
          (op ((b f).obj U)) ≫
        (pullComp f g k hk F).hom.hom.app (op ((b g).obj ((b f).obj U))) =
      ((adj k).unit.app F).hom.app (op U) ≫
        ((Scheme.etaleSetPullback k).obj F).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
            g f k hk.symm).inv.app U).op := by
  subst k
  apply ConcreteCategory.hom_ext
  intro s
  exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1 R S T f g F U s

private noncomputable def relativeProjection {X : Scheme.{u}}
    {Y Z : X.ProEt} (g : Z ⟶ Y) (V : Y.left.Etale) :
    (localSite Z).obj ((b g.left).obj V) ⟶ (localSite Y).obj V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom g.left) (by
    change pullback.fst V.hom g.left ≫ (V.hom ≫ Y.hom) =
      (pullback.snd V.hom g.left ≫ Z.hom)
    have hg : g.left ≫ Y.hom = Z.hom := g.w
    rw [← Category.assoc, pullback.condition, Category.assoc, hg])

private noncomputable def localTransition {X : Scheme.{u}}
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    {Y Z : X.ProEt} (g : Z ⟶ Y) :
    localSheaf G Y ⟶ (push g.left).obj (localSheaf G Z) := ⟨{
  app V := G.obj.map (relativeProjection g V.unop).op
  naturality := by
    intro U V h
    change G.obj.map ((localSite Y).map h.unop).op ≫
        G.obj.map (relativeProjection g V.unop).op =
      G.obj.map (relativeProjection g U.unop).op ≫
        G.obj.map ((localSite Z).map ((b g.left).map h.unop)).op
    rw [← G.obj.map_comp, ← G.obj.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change pullback.fst V.unop.hom g.left ≫ h.unop.left =
      ((b g.left).map h.unop).left ≫ pullback.fst U.unop.hom g.left
    simp [MorphismProperty.Over.pullback_map_left]
}⟩

private noncomputable def localTransitionTranspose {X : Scheme.{u}}
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    {Y Z : X.ProEt} (g : Z ⟶ Y) :
    (Scheme.etaleSetPullback g.left).obj (localSheaf G Y) ⟶ localSheaf G Z :=
  ((adj g.left).homEquiv (localSheaf G Y) (localSheaf G Z)).symm
    (localTransition G g)

private lemma localTransition_unit {X : Scheme.{u}}
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    {Y Z : X.ProEt} (g : Z ⟶ Y) (V : Y.left.Etale) :
    ((adj g.left).unit.app (localSheaf G Y)).hom.app (op V) ≫
        (localTransitionTranspose G g).hom.app (op ((b g.left).obj V)) =
      G.obj.map (relativeProjection g V).op := by
  have h := ((adj g.left).homEquiv (localSheaf G Y) (localSheaf G Z)).apply_symm_apply
    (localTransition G g)
  exact congrArg (fun f ↦ f.hom.app (op V)) h

private lemma terminalTransport_inv {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (k : T ⟶ R) (hk : g ≫ f = k)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    (etaleSetTerminalTransport f g k hk F).inv =
      ((Scheme.etaleSetPullback g).obj ((Scheme.etaleSetPullback f).obj F)).obj.map
        (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) g))
          (Category.comp_id _)).inv.op ≫
      (pullComp f g k hk F).hom.hom.app (op (Scheme.Etale.mk (𝟙 T))) := by
  subst k
  simp only [etaleSetTerminalTransport, pullComp, eqToIso_refl, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_inv, Iso.op_inv, asIso_hom,
    Iso.trans_hom, Iso.refl_hom, Category.comp_id]
  rfl

-- Pasting the two local adjunctions gives naturality of the extension.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma localTranspose_pasting {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    {Y Z : X.ProEt} (g : Z ⟶ Y) :
    (Scheme.etaleSetPullback g.left).map (localTranspose F G α Y) ≫
        localTransitionTranspose G g =
      (pullComp Y.hom g.left Z.hom g.w F).hom ≫ localTranspose F G α Z := by
  let FY := (Scheme.etaleSetPullback Y.hom).obj F
  let TY := localTranspose F G α Y
  let TZ := localTranspose F G α Z
  let TT := localTransitionTranspose G g
  let c := pullComp Y.hom g.left Z.hom g.w F
  have key (U : X.Etale) :
      ((adj Y.hom).unit.app F).hom.app (op U) ≫
          ((adj g.left).unit.app FY).hom.app (op ((b Y.hom).obj U)) ≫
          (((Scheme.etaleSetPullback g.left).map TY) ≫ TT).hom.app
            (op ((b g.left).obj ((b Y.hom).obj U))) =
        ((adj Y.hom).unit.app F).hom.app (op U) ≫
          ((adj g.left).unit.app FY).hom.app (op ((b Y.hom).obj U)) ≫
          (c.hom ≫ TZ).hom.app (op ((b g.left).obj ((b Y.hom).obj U))) := by
    let V := (b Y.hom).obj U
    let W := (b g.left).obj V
    let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      g.left Y.hom Z.hom g.w.symm).inv.app U
    have hn := NatTrans.congr_app (congrArg (fun q ↦ q.hom)
      ((adj g.left).unit.naturality TY)) (op V)
    change TY.hom.app (op V) ≫ ((adj g.left).unit.app (localSheaf G Y)).hom.app
        (op V) = ((adj g.left).unit.app FY).hom.app (op V) ≫
        ((Scheme.etaleSetPullback g.left).map TY).hom.app (op W) at hn
    change _ ≫ _ ≫ (((Scheme.etaleSetPullback g.left).map TY).hom.app (op W) ≫
        TT.hom.app (op W)) = _ ≫ _ ≫ (c.hom.hom.app (op W) ≫ TZ.hom.app (op W))
    rw [← reassoc_of% hn]
    rw [reassoc_of% (localTranspose_unit F G α Y U)]
    have ht := localTransition_unit G g V
    change ((adj g.left).unit.app (localSheaf G Y)).hom.app (op V) ≫
      TT.hom.app (op W) = G.obj.map (relativeProjection g V).op at ht
    rw [ht]
    have hc := pullComp_unit Y.hom g.left Z.hom g.w F U
    change ((adj Y.hom).unit.app F).hom.app (op U) ≫
      ((adj g.left).unit.app FY).hom.app (op V) ≫ c.hom.hom.app (op W) =
      ((adj Z.hom).unit.app F).hom.app (op U) ≫
        ((Scheme.etaleSetPullback Z.hom).obj F).obj.map p.op at hc
    rw [reassoc_of% hc]
    have hz := TZ.hom.naturality p.op
    change ((Scheme.etaleSetPullback Z.hom).obj F).obj.map p.op ≫
      TZ.hom.app (op W) = TZ.hom.app (op ((b Z.hom).obj U)) ≫
        G.obj.map ((localSite Z).map p).op at hz
    rw [hz]
    rw [reassoc_of% (localTranspose_unit F G α Z U)]
    change (α.hom.app (op U) ≫ G.obj.map (projection Y U).op) ≫
        G.obj.map (relativeProjection g V).op =
      (α.hom.app (op U) ≫ G.obj.map (projection Z U).op) ≫
        G.obj.map ((localSite Z).map p).op
    simp only [Category.assoc, ← G.obj.map_comp, ← op_comp]
    congr 2
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change pullback.fst V.hom g.left ≫ pullback.fst U.hom Y.hom =
      p.left ≫ pullback.fst U.hom Z.hom
    simp [p, V, MorphismProperty.Over.pullbackComp_inv_app_left]
  apply (((adj Y.hom).comp (adj g.left)).homEquiv F (localSheaf G Z)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U s
  obtain ⟨U⟩ := U
  convert ConcreteCategory.congr_hom (key U) s using 1 <;> rfl

private def identityIso {X : Scheme.{u}} (Y : X.ProEt) :
    (localSite Y).obj (Scheme.Etale.mk (𝟙 Y.left)) ≅ Y :=
  MorphismProperty.Over.isoMk (Iso.refl Y.left) (by
    change 𝟙 Y.left ≫ Y.hom = 𝟙 Y.left ≫ Y.hom
    rfl)

private noncomputable def sectionMap {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (Y : X.ProEt) :
    ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.left))) → G.obj.obj (op Y) :=
  fun t ↦ G.obj.map (identityIso Y).inv.op
    ((localTranspose F G α Y).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) t)

private lemma sectionMap_diagonal {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    (U : X.Etale) (s : F.obj.obj (op U)) :
    sectionMap F G α ((Scheme.toProEt X).obj U) (δ[X, F, U] s) =
      α.hom.app (op U) s := by
  rcases U with ⟨⟨S, ⟨⟨⟩⟩, f⟩, hf⟩
  change S ⟶ X at f
  let _ : Etale f := hf
  let U := Scheme.Etale.mk f
  let Y := (Scheme.toProEt X).obj U
  let d : Scheme.Etale.mk (𝟙 U.left) ⟶ (b U.hom).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp)) (by simp)
  have hn := (localTranspose F G α Y).hom.naturality d.op
  change ((Scheme.etaleSetPullback U.hom).obj F).obj.map d.op ≫
      (localTranspose F G α Y).hom.app (op (Scheme.Etale.mk (𝟙 U.left))) =
    (localTranspose F G α Y).hom.app (op ((b U.hom).obj U)) ≫
      G.obj.map ((localSite Y).map d).op at hn
  have h : ((adj U.hom).unit.app F).hom.app (op U) ≫
      ((Scheme.etaleSetPullback U.hom).obj F).obj.map d.op ≫
      (localTranspose F G α Y).hom.app (op (Scheme.Etale.mk (𝟙 U.left))) ≫
      G.obj.map (identityIso Y).inv.op = α.hom.app (op U) := by
    rw [reassoc_of% hn]
    have hu := localTranspose_unit F G α Y U
    change ((adj U.hom).unit.app F).hom.app (op U) ≫
      (localTranspose F G α Y).hom.app (op ((b U.hom).obj U)) =
      α.hom.app (op U) ≫ G.obj.map (projection Y U).op at hu
    rw [reassoc_of% hu]
    simp only [← Functor.map_comp, ← op_comp]
    have hi : (identityIso Y).inv ≫ (localSite Y).map d ≫ projection Y U = 𝟙 Y := by
      apply MorphismProperty.Over.Hom.ext
      change 𝟙 U.left ≫ (pullback.lift (𝟙 U.left) (𝟙 U.left) _) ≫
        pullback.fst U.hom U.hom = 𝟙 U.left
      simp
    simp only [Category.assoc]
    rw [hi, op_id]
    erw [G.obj.map_id]
    exact Category.comp_id _
  convert ConcreteCategory.congr_hom h s using 1 <;> rfl

private lemma sectionMap_naturality {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (α : F ⟶ ((Scheme.toProEt X).sheafPushforwardContinuous
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj G)
    {Y Z : X.ProEt} (g : Z ⟶ Y)
    (t : ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.left)))) :
    sectionMap F G α Z
        ((((adj g.left).unit.app ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
          (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) t) =
      G.obj.map g.op (sectionMap F G α Y t) := by
  let FY := (Scheme.etaleSetPullback Y.hom).obj F
  let TY := localTranspose F G α Y
  let TZ := localTranspose F G α Z
  let TT := localTransitionTranspose G g
  let IY := Scheme.Etale.mk (𝟙 Y.left)
  let IZ := Scheme.Etale.mk (𝟙 Z.left)
  let i : (b g.left).obj IY ≅ IZ :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y.left) g.left)) (Category.comp_id _)
  let c := pullComp Y.hom g.left Z.hom g.w F
  have hp := congrArg (fun f ↦ f.hom.app (op IZ)) (localTranspose_pasting F G α g)
  change ((Scheme.etaleSetPullback g.left).map TY).hom.app (op IZ) ≫
      TT.hom.app (op IZ) = c.hom.hom.app (op IZ) ≫ TZ.hom.app (op IZ) at hp
  have hn := ((Scheme.etaleSetPullback g.left).map TY).hom.naturality i.inv.op
  have hu := NatTrans.congr_app (congrArg (fun f ↦ f.hom)
    ((adj g.left).unit.naturality TY)) (op IY)
  change TY.hom.app (op IY) ≫
      ((adj g.left).unit.app (localSheaf G Y)).hom.app (op IY) =
    ((adj g.left).unit.app FY).hom.app (op IY) ≫
      ((Scheme.etaleSetPullback g.left).map TY).hom.app (op ((b g.left).obj IY)) at hu
  have ht := TT.hom.naturality i.inv.op
  have he : ((adj g.left).unit.app FY).hom.app (op IY) ≫
      ((Scheme.etaleSetPullback g.left).obj FY).obj.map i.inv.op ≫
      c.hom.hom.app (op IZ) ≫ TZ.hom.app (op IZ) ≫ G.obj.map (identityIso Z).inv.op =
    TY.hom.app (op IY) ≫ G.obj.map (identityIso Y).inv.op ≫ G.obj.map g.op := by
    rw [← reassoc_of% hp, reassoc_of% hn, ← reassoc_of% hu, reassoc_of% ht]
    have hunit := localTransition_unit G g IY
    change ((adj g.left).unit.app (localSheaf G Y)).hom.app (op IY) ≫
      TT.hom.app (op ((b g.left).obj IY)) = G.obj.map (relativeProjection g IY).op at hunit
    rw [reassoc_of% hunit]
    change TY.hom.app (op IY) ≫ G.obj.map (relativeProjection g IY).op ≫
      G.obj.map ((localSite Z).map i.inv).op ≫ G.obj.map (identityIso Z).inv.op = _
    simp only [← G.obj.map_comp, ← op_comp, Category.assoc]
    congr 2
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 Z.left ≫ i.inv.left) ≫ pullback.fst (𝟙 Y.left) g.left = g.left ≫ 𝟙 Y.left
    dsimp [i]
    simp
  have htransport := terminalTransport_inv Y.hom g.left Z.hom g.w F
  rw [htransport]
  convert ConcreteCategory.congr_hom he t using 1 <;> rfl

-- For uniqueness, turn local Kan representatives into diagonal restrictions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def terminalLift {X T : Scheme.{u}} (f : T ⟶ X)
    (U : X.Etale) (t : T ⟶ U.left) (ht : t ≫ U.hom = f) :
    Scheme.Etale.mk (𝟙 T) ⟶ (b f).obj U :=
  MorphismProperty.Over.homMk (pullback.lift t (𝟙 T) (by simpa using ht)) (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma diagonal_transition {X T : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (t : T ⟶ U.left) (k : T ⟶ X) (hk : t ≫ U.hom = k) (s : F.obj.obj (op U)) :
    ((Scheme.etaleSetPullback k).obj F).obj.map (terminalLift k U t hk).op
        (((adj k).unit.app F).hom.app (op U) s) =
      (((adj t).unit.app ((Scheme.etaleSetPullback U.hom).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 U.left))) ≫
        (etaleSetTerminalTransport U.hom t k hk F).inv) (δ[X, F, U] s) := by
  subst k
  let f := U.hom
  let I := Scheme.Etale.mk (𝟙 U.left)
  let J := Scheme.Etale.mk (𝟙 T)
  let d := terminalLift f U (𝟙 U.left) (by simp [f])
  let d' := terminalLift (t ≫ f) U t rfl
  let i : (b t).obj I ≅ J :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 U.left) t)) (Category.comp_id _)
  let m := i.inv ≫ (b t).map d
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) t f).inv.app U
  let LF := (Scheme.etaleSetPullback f).obj F
  let LTF := (Scheme.etaleSetPullback t).obj LF
  let LKF := (Scheme.etaleSetPullback (t ≫ f)).obj F
  let c := pullComp f t (t ≫ f) rfl F
  let ηf := ((adj f).unit.app F).hom
  let ηt := ((adj t).unit.app LF).hom
  let ηk := ((adj (t ≫ f)).unit.app F).hom
  have hn : LF.obj.map d.op ≫ ηt.app (op I) =
      ηt.app (op ((b f).obj U)) ≫ LTF.obj.map ((b t).map d).op :=
    ηt.naturality d.op
  have hc : LTF.obj.map m.op ≫ c.hom.hom.app (op J) =
      c.hom.hom.app (op ((b t).obj ((b f).obj U))) ≫ LKF.obj.map m.op :=
    c.hom.hom.naturality m.op
  have hu : ηf.app (op U) ≫ ηt.app (op ((b f).obj U)) ≫
      c.hom.hom.app (op ((b t).obj ((b f).obj U))) =
        ηk.app (op U) ≫ LKF.obj.map p.op := pullComp_unit f t (t ≫ f) rfl F U
  have hp : m ≫ p = d' := by
    apply MorphismProperty.Over.Hom.ext
    change m.left ≫ p.left = d'.left
    dsimp [m, p, d, d', i, terminalLift, I]
    rw [MorphismProperty.Over.pullbackComp_inv_app_left]
    apply pullback.hom_ext <;>
      simp [Category.assoc, pullback_inv_snd_fst_of_left_isIso]
    all_goals rfl
  have key : ηf.app (op U) ≫ LF.obj.map d.op ≫ ηt.app (op I) ≫
      LTF.obj.map i.inv.op ≫ c.hom.hom.app (op J) =
        ηk.app (op U) ≫ LKF.obj.map d'.op := by
    calc
      _ = ηf.app (op U) ≫ ηt.app (op ((b f).obj U)) ≫
          LTF.obj.map m.op ≫ c.hom.hom.app (op J) := by
        rw [reassoc_of% hn]
        simp only [m, op_comp, Functor.map_comp, Category.assoc]
      _ = ηf.app (op U) ≫ ηt.app (op ((b f).obj U)) ≫
          c.hom.hom.app (op ((b t).obj ((b f).obj U))) ≫ LKF.obj.map m.op := by
        rw [hc]
      _ = ηk.app (op U) ≫ LKF.obj.map (m ≫ p).op := by
        rw [reassoc_of% hu]
        simp only [op_comp, Functor.map_comp]
      _ = _ := by rw [hp]
  rw [terminalTransport_inv]
  convert (ConcreteCategory.congr_hom key s).symm using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma terminal_unit_restrict {T : Scheme.{u}}
    (H : Sheaf T.smallEtaleTopology (Type (u + 1))) (V : T.Etale)
    (i : V ⟶ Scheme.Etale.mk (𝟙 T)) :
    ((adj V.hom).unit.app H).hom.app (op (Scheme.Etale.mk (𝟙 T))) ≫
        ((Scheme.etaleSetPullback V.hom).obj H).obj.map
          (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 T) V.hom))
            (Category.comp_id _)).inv.op =
      H.obj.map i.op ≫ ((adj V.hom).unit.app H).hom.app (op V) ≫
        ((Scheme.etaleSetPullback V.hom).obj H).obj.map
          (terminalLift V.hom V (𝟙 V.left) (by simp)).op := by
  have hn := ((adj V.hom).unit.app H).hom.naturality i.op
  change H.obj.map i.op ≫ ((adj V.hom).unit.app H).hom.app (op V) =
    ((adj V.hom).unit.app H).hom.app (op (Scheme.Etale.mk (𝟙 T))) ≫
      ((Scheme.etaleSetPullback V.hom).obj H).obj.map ((b V.hom).map i).op at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  have hi : i.left = V.hom := (Category.comp_id i.left).symm.trans i.w
  change (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 T) V.hom))
    (Category.comp_id _)).inv.left =
    (terminalLift V.hom V (𝟙 V.left) (by simp)).left ≫ ((b V.hom).map i).left
  rw [MorphismProperty.Over.pullback_map_left]
  dsimp [terminalLift]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [pullback_inv_snd_fst_of_left_isIso]
    simp [hi]
  · simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma unit_lift_composition {X T : Scheme.{u}} (f : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (V : T.Etale) (W : X.Etale)
    (a : V ⟶ (b f).obj W) :
    let t := a.left ≫ pullback.fst W.hom f
    let ht : t ≫ W.hom = V.hom ≫ f := by
      dsimp [t]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun z ↦ z ≫ f) a.w
    ((adj f).unit.app F).hom.app (op W) ≫
        ((Scheme.etaleSetPullback f).obj F).obj.map a.op ≫
        ((adj V.hom).unit.app ((Scheme.etaleSetPullback f).obj F)).hom.app (op V) ≫
        ((Scheme.etaleSetPullback V.hom).obj ((Scheme.etaleSetPullback f).obj F)).obj.map
          (terminalLift V.hom V (𝟙 V.left) (by simp)).op ≫
        (pullComp f V.hom (V.hom ≫ f) rfl F).hom.hom.app
          (op (Scheme.Etale.mk (𝟙 V.left))) =
      ((adj (V.hom ≫ f)).unit.app F).hom.app (op W) ≫
        ((Scheme.etaleSetPullback (V.hom ≫ f)).obj F).obj.map
          (terminalLift (V.hom ≫ f) W t ht).op := by
  dsimp only
  let LF := (Scheme.etaleSetPullback f).obj F
  let LGF := (Scheme.etaleSetPullback V.hom).obj LF
  let LKF := (Scheme.etaleSetPullback (V.hom ≫ f)).obj F
  let d := terminalLift V.hom V (𝟙 V.left) (by simp)
  let m := d ≫ (b V.hom).map a
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) V.hom f).inv.app W
  let c := pullComp f V.hom (V.hom ≫ f) rfl F
  have hn := ((adj V.hom).unit.app LF).hom.naturality a.op
  change LF.obj.map a.op ≫ ((adj V.hom).unit.app LF).hom.app (op V) =
    ((adj V.hom).unit.app LF).hom.app (op ((b f).obj W)) ≫
      LGF.obj.map ((b V.hom).map a).op at hn
  rw [reassoc_of% hn]
  change _ ≫ _ ≫ LGF.obj.map ((b V.hom).map a).op ≫ LGF.obj.map d.op ≫ _ = _
  rw [← Functor.map_comp_assoc, ← op_comp]
  change _ ≫ _ ≫ LGF.obj.map m.op ≫ c.hom.hom.app _ = _
  rw [c.hom.hom.naturality m.op]
  rw [reassoc_of% (pullComp_unit f V.hom (V.hom ≫ f) rfl F W)]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change (d.left ≫ ((b V.hom).map a).left) ≫ p.left = _
  rw [MorphismProperty.Over.pullback_map_left]
  dsimp [d, terminalLift, p]
  rw [MorphismProperty.Over.pullbackComp_inv_app_left]
  apply pullback.hom_ext <;> simp [Category.assoc]

private lemma transition_representative {X T : Scheme.{u}} (f : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback f).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (V : T.Etale) (i : V ⟶ Scheme.Etale.mk (𝟙 T))
    (W : X.Etale) (a : V ⟶ (b f).obj W) (s : F.obj.obj (op W))
    (hs : ((Scheme.etaleSetPullback f).obj F).obj.map i.op t =
      ((Scheme.etaleSetPullback f).obj F).obj.map a.op
        (((adj f).unit.app F).hom.app (op W) s)) :
    let r := a.left ≫ pullback.fst W.hom f
    let hr : r ≫ W.hom = V.hom ≫ f := by
      dsimp [r]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun z ↦ z ≫ f) a.w
    (((adj V.hom).unit.app ((Scheme.etaleSetPullback f).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 T))) ≫
        (etaleSetTerminalTransport f V.hom (V.hom ≫ f) rfl F).inv) t =
      ((Scheme.etaleSetPullback (V.hom ≫ f)).obj F).obj.map
        (terminalLift (V.hom ≫ f) W r hr).op
          (((adj (V.hom ≫ f)).unit.app F).hom.app (op W) s) := by
  dsimp only
  let LF := (Scheme.etaleSetPullback f).obj F
  let LGF := (Scheme.etaleSetPullback V.hom).obj LF
  let q := (pullComp f V.hom (V.hom ≫ f) rfl F).hom.hom.app
    (op (Scheme.Etale.mk (𝟙 V.left)))
  let ρ := ((adj V.hom).unit.app LF).hom.app (op V) ≫
    LGF.obj.map (terminalLift V.hom V (𝟙 V.left) (by simp)).op
  have h₁ := congrArg (fun z ↦ q z) (ConcreteCategory.congr_hom
    (terminal_unit_restrict LF V i) t)
  have h₂ := congrArg (fun z ↦ q (ρ z)) hs
  have h₃ := ConcreteCategory.congr_hom (unit_lift_composition f F V W a) s
  rw [terminalTransport_inv]
  convert h₁.trans (h₂.trans h₃) using 1 <;> rfl

private def localStructure {X : Scheme.{u}} (Y : X.ProEt) (V : Y.left.Etale) :
    (localSite Y).obj V ⟶ Y :=
  MorphismProperty.Over.homMk V.hom (by rfl)

private noncomputable def representingArrow {X : Scheme.{u}}
    (Y : X.ProEt) (V : Y.left.Etale) (W : X.Etale) (a : V ⟶ (b Y.hom).obj W) :
    (localSite Y).obj V ⟶ (Scheme.toProEt X).obj W :=
  MorphismProperty.Over.homMk (a.left ≫ pullback.fst W.hom Y.hom) (by
    change (a.left ≫ pullback.fst W.hom Y.hom) ≫ W.hom = V.hom ≫ Y.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ Y.hom) a.w)

-- Sheafification is locally surjective; the Kan extension has explicit representatives.
private lemma localRepresentatives {X T : Scheme.{u}} (f : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : T.Etale)
    (t : ((Scheme.etaleSetPullback f).obj F).obj.obj (op U)) :
    ∃ R : Sieve U, R ∈ T.smallEtaleTopology U ∧
      ∀ (V : T.Etale) (i : V ⟶ U), R i →
        ∃ (W : X.Etale) (k : V ⟶ (b f).obj W) (s : F.obj.obj (op W)),
          ((Scheme.etaleSetPullback f).obj F).obj.map i.op t =
            ((Scheme.etaleSetPullback f).obj F).obj.map k.op
              (((adj f).unit.app F).hom.app (op W) s) := by
  let Q := (b f).op.lan.obj F.obj
  let R := Presheaf.imageSieve (toSheafify T.smallEtaleTopology Q) t
  refine ⟨R, Presheaf.imageSieve_mem T.smallEtaleTopology
    (toSheafify T.smallEtaleTopology Q) t, ?_⟩
  intro V i hi
  obtain ⟨p, hp⟩ := hi
  obtain ⟨W, k, s, hs⟩ :=
    etaleInverseImageSectionDescription_representation X T f F V p
  exact ⟨W, k, s, hp.symm.trans hs⟩

private lemma local_diagonal_representatives {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (H : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ Y : X.ProEt, H.obj.obj (op Y) ≃
      ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (Y Z : X.ProEt) (g : Z ⟶ Y) (s : H.obj.obj (op Y)),
      e Z (H.obj.map g.op s) =
        (((adj g.left).unit.app ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
          (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e Y s))
    (Y : X.ProEt) (s : H.obj.obj (op Y)) :
    ∃ R : Sieve (Scheme.Etale.mk (𝟙 Y.left)),
      R ∈ Y.left.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y.left)) ∧
        ∀ (V : Y.left.Etale) (i : V ⟶ Scheme.Etale.mk (𝟙 Y.left)), R i →
          ∃ (W : X.Etale) (r : (localSite Y).obj V ⟶ (Scheme.toProEt X).obj W)
            (t : F.obj.obj (op W)),
            H.obj.map (localStructure Y V).op s =
              H.obj.map r.op ((e ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t)) := by
  obtain ⟨R, hR, hrep⟩ := localRepresentatives Y.hom F
    (Scheme.Etale.mk (𝟙 Y.left)) (e Y s)
  refine ⟨R, hR, ?_⟩
  intro V i hi
  obtain ⟨W, a, t, ht⟩ := hrep V i hi
  let Z := (localSite Y).obj V
  let p := localStructure Y V
  let r := representingArrow Y V W a
  refine ⟨W, r, t, ?_⟩
  apply (e Z).injective
  rw [hres Y Z p, hres ((Scheme.toProEt X).obj W) Z r, Equiv.apply_symm_apply]
  have hl := transition_representative Y.hom F (e Y s) V i W a t ht
  have hd := diagonal_transition F W r.left Z.hom r.w t
  exact hl.trans hd

/-- Precomposition with the concrete diagonal unit is bijective on morphisms.
This is a unique-extension statement about an already constructed map, without
asserting an adjunction or any natural hom-set equivalence. -/
theorem proEtaleComparisonSectionUnit_bijective (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
      (A.obj F).obj.obj (op Y) ≃
        ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
      e F Z ((A.obj F).obj.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e F Y s))
    (hfun : ∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
      e F' Y ((A.map ψ).hom.app (op Y) s) =
        ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
    Function.Bijective (fun f : A.obj F ⟶ G ↦
      (proEtaleComparisonSectionUnit X A e hres hfun).app F ≫
        ((Scheme.toProEt X).sheafPushforwardContinuous
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).map f) := by
  constructor
  · intro β γ h
    have hdiag (W : X.Etale) (t : F.obj.obj (op W)) :
        β.hom.app (op ((Scheme.toProEt X).obj W))
            ((e F ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t)) =
          γ.hom.app (op ((Scheme.toProEt X).obj W))
            ((e F ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t)) := by
      exact congrArg (fun f ↦ f.hom.app (op W) t) h
    ext Y s
    obtain ⟨Y⟩ := Y
    obtain ⟨R, hR, hrep⟩ := local_diagonal_representatives F (A.obj F) (e F)
      (hres F) Y s
    apply ((G.obj.mapIso (identityIso Y).symm.op).toEquiv).injective
    apply ((localSheaf G Y).property.isSheafFor R hR).isSeparatedFor.ext
    intro V i hi
    obtain ⟨W, r, t, ht⟩ := hrep V i hi
    have hp : (localSite Y).map i ≫ (identityIso Y).hom = localStructure Y V := by
      apply MorphismProperty.Over.Hom.ext
      exact i.w
    change G.obj.map ((localSite Y).map i).op
        (G.obj.map (identityIso Y).hom.op (β.hom.app (op Y) s)) =
      G.obj.map ((localSite Y).map i).op
        (G.obj.map (identityIso Y).hom.op (γ.hom.app (op Y) s))
    rw [← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply,
      ← op_comp, hp]
    calc
      G.obj.map (localStructure Y V).op (β.hom.app (op Y) s) =
          β.hom.app (op ((localSite Y).obj V))
            ((A.obj F).obj.map (localStructure Y V).op s) :=
        (β.hom.naturality_apply (localStructure Y V).op s).symm
      _ = β.hom.app (op ((localSite Y).obj V))
          ((A.obj F).obj.map r.op
            ((e F ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t))) :=
        congrArg _ ht
      _ = G.obj.map r.op (β.hom.app (op ((Scheme.toProEt X).obj W))
          ((e F ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t))) :=
        β.hom.naturality_apply r.op _
      _ = G.obj.map r.op (γ.hom.app (op ((Scheme.toProEt X).obj W))
          ((e F ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t))) :=
        congrArg _ (hdiag W t)
      _ = γ.hom.app (op ((localSite Y).obj V))
          ((A.obj F).obj.map r.op
            ((e F ((Scheme.toProEt X).obj W)).symm (δ[X, F, W] t))) :=
        (γ.hom.naturality_apply r.op _).symm
      _ = γ.hom.app (op ((localSite Y).obj V))
          ((A.obj F).obj.map (localStructure Y V).op s) :=
        congrArg _ ht.symm
      _ = G.obj.map (localStructure Y V).op (γ.hom.app (op Y) s) :=
        γ.hom.naturality_apply (localStructure Y V).op s
  · intro α
    let β : A.obj F ⟶ G := ⟨{
      app Y := ↾fun s ↦ sectionMap F G α Y.unop (e F Y.unop s)
      naturality := by
        intro Y Z g
        apply ConcreteCategory.hom_ext
        intro s
        change sectionMap F G α Z.unop (e F Z.unop ((A.obj F).obj.map g s)) =
          G.obj.map g (sectionMap F G α Y.unop (e F Y.unop s))
        have hr := congrArg (sectionMap F G α Z.unop)
          (hres F Y.unop Z.unop g.unop s)
        exact hr.trans (sectionMap_naturality F G α g.unop (e F Y.unop s))
    }⟩
    refine ⟨β, ?_⟩
    ext U s
    change sectionMap F G α ((Scheme.toProEt X).obj U.unop)
      (e F ((Scheme.toProEt X).obj U.unop)
        ((e F ((Scheme.toProEt X).obj U.unop)).symm (δ[X, F, U.unop] s))) = _
    rw [Equiv.apply_symm_apply]
    exact sectionMap_diagonal F G α U.unop s

end AlgebraicGeometry
