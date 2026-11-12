import Langlands.Sheaf.Renard.InverseImageComparison
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Original stalk comparison for equivariant inverse image

The map on stalks is induced by the actual Kan-extension and sheafification
units. Its equivariance follows from the existing group-labelled germ maps.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions.InverseImageStalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant

variable {G X Y : Type} [Group G]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [MulAction G Y]
variable [ContinuousConstSMul G X] [ContinuousConstSMul G Y]
variable (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The stalk map induced by an original equivariant map to direct image. -/
def preimageStalkMap
    {F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ}
    {F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ}
    (k : F ⟶ (DirectImage.preimage f hf).op ⋙ F') (x : X) :
    ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F).stalk (f x) ⟶
      ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj F').stalk x :=
  (TopCat.Presheaf.stalkFunctor (X := TopCat.of Y) (ModuleCat.{0} ℂ) (f x)).map
      (Functor.whiskerLeft (ActionOpens.inclusion G Y).op k) ≫
    TopCat.Presheaf.stalkPushforward (ModuleCat.{0} ℂ) (TopCat.ofHom f)
      ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj F') x

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
/-- The induced map sends every original germ by the original section map. -/
@[reassoc]
theorem germ_preimageStalkMap
    {F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ}
    {F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ}
    (k : F ⟶ (DirectImage.preimage f hf).op ⋙ F') (x : X)
    (U : Opens Y) (hx : f x ∈ U) :
    ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F).germ U (f x) hx ≫
        preimageStalkMap f hf k x =
      k.app (op ⟨U⟩) ≫ ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj F').germ
        ((Opens.map (TopCat.ofHom f)).obj U) x hx := by
  rw [preimageStalkMap, TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  exact congrArg (fun a => k.app (op ⟨U⟩) ≫ a)
    (TopCat.Presheaf.stalkPushforward_germ (ModuleCat.{0} ℂ) (TopCat.ofHom f)
      ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj F') U x hx)

/-- Original labelled transport commutes with the induced stalk map. -/
@[reassoc]
theorem preimageStalkMap_transport
    {F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ}
    {F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ}
    (k : F ⟶ (DirectImage.preimage f hf).op ⋙ F')
    (g : G) (x x' : X) (h : g • x = x') :
    Godement.stalkPull F g (f x) (f x') (by rw [← hf, h]) ≫
        preimageStalkMap f hf k x =
      preimageStalkMap f hf k x' ≫ Godement.stalkPull F' g x x' h := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx'
  have hx : f x ∈ Godement.preimageOpen g U := by
    change g • f x ∈ U
    rw [← hf, h]
    exact hx'
  rw [Godement.germ_stalkPull_assoc, germ_preimageStalkMap,
    germ_preimageStalkMap_assoc]
  have step := Godement.germ_stalkPull_arrow F'
    ((DirectImage.preimage f hf).map (Godement.preimageArrow g U)) x x' h hx
  exact (k.naturality_assoc (Godement.preimageArrow g U).op _).trans
    (congrArg (fun a => k.app (op ⟨U⟩) ≫ a) step.symm)

omit [ContinuousConstSMul G X] in
/-- The transport Kan-extension stalk map agrees with the ordinary one
after the canonical comparison. -/
theorem kanStalkMap_comparison (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (x : X) :
    preimageStalkMap f hf ((DirectImage.preimage f hf).op.lanUnit.app F) x ≫
        (TopCat.Presheaf.stalkFunctor (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map
          (InverseImageComparison.presheafObjectIso f hf F).hom =
      TopCat.Presheaf.stalkPullbackHom (ModuleCat.{0} ℂ) (TopCat.ofHom f)
        ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F) x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [germ_preimageStalkMap_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  have h := NatTrans.congr_app
    (InverseImageComparison.restrictedUnit_presheafObjectIso_hom f hf F) (op U)
  have h' := congrArg (fun a => a ≫
      ((TopCat.Presheaf.pullback (ModuleCat.{0} ℂ) (TopCat.ofHom f)).obj
        ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F)).germ
          ((Opens.map (TopCat.ofHom f)).obj U) x hx) h
  have h'' := TopCat.Presheaf.germ_stalkPullbackHom (ModuleCat.{0} ℂ) (TopCat.ofHom f)
    ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F) x U hx
  simp only [TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit] at h''
  refine Eq.trans ?_ h''.symm
  simpa only [InverseImageComparison.restrictedUnit, underlyingPresheaf,
    TopCat.Presheaf.pullback, TopCat.Presheaf.stalk, Functor.op_obj, ActionOpens.inclusion,
    Functor.whiskeringLeft_obj_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.id_obj, Category.assoc] using h'

instance kanStalkMap_isIso (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (x : X) :
    IsIso (preimageStalkMap f hf ((DirectImage.preimage f hf).op.lanUnit.app F) x) := by
  have : IsIso (TopCat.Presheaf.stalkPullbackHom (ModuleCat.{0} ℂ) (TopCat.ofHom f)
      ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F) x) :=
    inferInstanceAs (IsIso (TopCat.Presheaf.stalkPullbackIso (ModuleCat.{0} ℂ) (TopCat.ofHom f)
      ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).obj F) x).hom)
  exact IsIso.of_isIso_fac_right (kanStalkMap_comparison f hf F x)

/-- Sheafification's actual unit on the underlying ordinary stalk. -/
def sheafifyStalkMap (P : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (x : X) :
    ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj P).stalk x ⟶
      (CompactSections.ordinary
        ((presheafToSheaf (transportTopology G X) (ModuleCat.{0} ℂ)).obj P).obj).stalk x :=
  (TopCat.Presheaf.stalkFunctor (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map
    (Functor.whiskerLeft (ActionOpens.inclusion G X).op
      (toSheafify (transportTopology G X) P))

instance sheafifyStalkMap_isIso
    (P : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (x : X) :
    IsIso (sheafifyStalkMap P x) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (X := TopCat.of X)
    x (ModuleCat.{0} ℂ)
    ((ActionOpens.inclusion G X).op ⋙ P)
  have : IsIso (((ActionOpens.inclusion G X).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{0} ℂ) (Opens.grothendieckTopology X) (transportTopology G X)).hom.app P).hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} ℂ)).map
        (((ActionOpens.inclusion G X).pushforwardContinuousSheafificationCompatibility
          (ModuleCat.{0} ℂ) (Opens.grothendieckTopology X) (transportTopology G X)).hom.app P)))
  unfold sheafifyStalkMap
  rw [← (ActionOpens.inclusion G X).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{0} ℂ) (Opens.grothendieckTopology X) (transportTopology G X) P,
    Functor.map_comp]
  infer_instance

/-- The original Kan-extension unit followed by the original sheafification unit. -/
def unit (F : ActionSheaf G Y) :
    F.obj ⟶ (DirectImage.preimage f hf).op ⋙ ((actionInverseImage f hf).obj F).obj :=
  (DirectImage.preimage f hf).op.lanUnit.app F.obj ≫
    Functor.whiskerLeft (DirectImage.preimage f hf).op
      (toSheafify (transportTopology G X) ((DirectImage.preimage f hf).op.lan.obj F.obj))

/-- The inverse-image map on the original stalks. -/
def stalkMap (F : ActionSheaf G Y) (x : X) :
    (CompactSections.ordinary F.obj).stalk (f x) ⟶
      (CompactSections.ordinary ((actionInverseImage f hf).obj F).obj).stalk x :=
  preimageStalkMap f hf (unit f hf F) x

/-- The stalk map factors through the actual unsheafified Kan extension. -/
theorem stalkMap_factor (F : ActionSheaf G Y) (x : X) :
    stalkMap f hf F x =
      preimageStalkMap f hf ((DirectImage.preimage f hf).op.lanUnit.app F.obj) x ≫
        sheafifyStalkMap ((DirectImage.preimage f hf).op.lan.obj F.obj) x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [stalkMap, germ_preimageStalkMap, germ_preimageStalkMap_assoc]
  change _ = _ ≫ _ ≫ (TopCat.Presheaf.stalkFunctor
    (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map _
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

instance stalkMap_isIso (F : ActionSheaf G Y) (x : X) : IsIso (stalkMap f hf F x) := by
  rw [stalkMap_factor]
  infer_instance

/-- The canonical comparison of actual ordinary stalks for equivariant inverse image. -/
def stalkIso (F : ActionSheaf G Y) (x : X) :
    (CompactSections.ordinary F.obj).stalk (f x) ≅
      (CompactSections.ordinary ((actionInverseImage f hf).obj F).obj).stalk x :=
  asIso (stalkMap f hf F x)

/-- The stalk comparison has the original unit's formula on every germ. -/
@[reassoc]
theorem germ_stalkIso_hom (F : ActionSheaf G Y) (x : X) (U : Opens Y) (hx : f x ∈ U) :
    (CompactSections.ordinary F.obj).germ U (f x) hx ≫ (stalkIso f hf F x).hom =
      (unit f hf F).app (op ⟨U⟩) ≫
        (CompactSections.ordinary ((actionInverseImage f hf).obj F).obj).germ
          ((Opens.map (TopCat.ofHom f)).obj U) x hx :=
  germ_preimageStalkMap f hf (unit f hf F) x U hx

/-- The actual inverse-image unit is natural in the original action sheaf. -/
theorem unit_naturality {F F' : ActionSheaf G Y} (k : F ⟶ F') :
    unit f hf F ≫ Functor.whiskerLeft (DirectImage.preimage f hf).op
        ((actionInverseImage f hf).map k).hom =
      k.hom ≫ unit f hf F' := by
  have h := (((DirectImage.preimage f hf).op.lanAdjunction (ModuleCat.{0} ℂ)).comp
    (sheafificationAdjunction (transportTopology G X) (ModuleCat.{0} ℂ))).unit.naturality k.hom
  apply NatTrans.ext
  funext U
  simpa only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, Functor.comp_map, Functor.id_map,
    NatTrans.comp_app, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.id_obj, actionInverseImage,
    Functor.sheafPullbackConstruction.sheafPullback, sheafEquivalence,
    ObjectProperty.ιOfLE, sheafToPresheaf, ObjectProperty.ι,
    inducedFunctor, ObjectProperty.homMk, Functor.whiskeringLeft_obj_obj,
    unit] using NatTrans.congr_app h.symm U

/-- Naturality of the original inverse-image stalk map. -/
@[reassoc]
theorem stalkMap_naturality {F F' : ActionSheaf G Y} (k : F ⟶ F') (x : X) :
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of Y) (ModuleCat.{0} ℂ) (f x)).map
        ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).map k.hom) ≫ stalkMap f hf F' x =
      stalkMap f hf F x ≫
        (TopCat.Presheaf.stalkFunctor (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map
          ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).map
            ((actionInverseImage f hf).map k).hom) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  simp only [stalkMap]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    germ_preimageStalkMap, germ_preimageStalkMap_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  have h := NatTrans.congr_app (unit_naturality f hf k) (op ⟨U⟩)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    underlyingPresheaf, CompactSections.ordinary, Functor.whiskeringLeft_obj_map,
    Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj,
    ActionOpens.inclusion, DirectImage.preimage] using
    congrArg (fun a => a ≫
      (CompactSections.ordinary ((actionInverseImage f hf).obj F').obj).germ
        ((Opens.map (TopCat.ofHom f)).obj U) x hx) h.symm

section FixedStalk

variable [TopologicalSpace G] [ContinuousSMul G X] [ContinuousSMul G Y]
variable (Q : Subgroup G) (x : X) (hfix : ∀ q : Q, (q : G) • x = x)

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y]
  [TopologicalSpace G] [ContinuousSMul G X] [ContinuousSMul G Y] in
include hf hfix in
/-- Equivariance carries every original fixed point to a fixed point. -/
theorem fixes_image (q : Q) : (q : G) • f x = f x := by
  rw [← hf, hfix]

/-- The canonical stalk comparison retains the two original stabilizer actions. -/
def fixedStalkIso (F : ActionSheaf G Y) :
    fixedStalkAction Q (f x) (fixes_image f hf Q x hfix) F ≅
      fixedStalkAction Q x hfix ((actionInverseImage f hf).obj F) :=
  Action.mkIso (stalkIso f hf F x) (fun q =>
    preimageStalkMap_transport f hf (unit f hf F) (q : G)⁻¹ x x (hfix q⁻¹))

/-- The stabilizer-stalk comparison is natural in the original action sheaf. -/
def fixedStalkActionsIso :
    fixedStalkActions Q (f x) (fixes_image f hf Q x hfix) ≅
      actionInverseImage f hf ⋙ fixedStalkActions Q x hfix :=
  NatIso.ofComponents (fixedStalkIso f hf Q x hfix) (fun k => by
    apply Action.Hom.ext
    exact stalkMap_naturality f hf k x)

/-- The same original comparison in the published representation category. -/
def fixedStalkFunctorIso :
    fixedStalkFunctor Q (f x) (fixes_image f hf Q x hfix) ≅
      actionInverseImage f hf ⋙ fixedStalkFunctor Q x hfix :=
  Functor.isoWhiskerRight (fixedStalkActionsIso f hf Q x hfix) (Rep.ActionToRep ℂ Q)

end FixedStalk

end Langlands.Sheaf.Renard.SectionActions.InverseImageStalks
