import Langlands.Sheaf.Renard.ActionInverseImage
import Langlands.Sheaf.Equivariant.Coinduction

/-!
# Ordinary inverse image underlying the action-sheaf inverse image

Ordinary comma objects form an equivalent indexing category for the transport
left Kan extension. Restriction also commutes with sheafification because the
inclusion of ordinary opens is continuous and cocontinuous.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions.InverseImageComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant

variable {G X Y : Type} [Group G]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [MulAction G Y]
variable [ContinuousConstSMul G X] [ContinuousConstSMul G Y]
variable (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Ordinary inverse-image comma objects are the objects with label one. -/
def commaInclusion (U : Opens X) :
    CostructuredArrow (Opens.map (TopCat.ofHom f)).op (op U) ⥤
      CostructuredArrow (DirectImage.preimage f hf).op
        (op ((ActionOpens.inclusion G X).obj U)) where
  obj j := CostructuredArrow.mk (Y := op ((ActionOpens.inclusion G Y).obj j.left.unop))
    (((ActionOpens.inclusion G X).map j.hom.unop).op)
  map m := CostructuredArrow.homMk
    (((ActionOpens.inclusion G Y).map m.left.unop).op) (by
      apply Quiver.Hom.unop_inj
      apply ActionOpens.Hom.ext
      change (1 : G) * 1 = 1
      exact one_mul 1)
  map_id _ := CostructuredArrow.ext _ _ (by
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    rfl)
  map_comp _ _ := CostructuredArrow.ext _ _ (by
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    exact (one_mul 1).symm)

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
/-- An arrow between two label-one comma objects has label one. -/
theorem commaInclusion_label_one (U : Opens X)
    {j k : CostructuredArrow (Opens.map (TopCat.ofHom f)).op (op U)}
    (m : (commaInclusion f hf U).obj j ⟶ (commaInclusion f hf U).obj k) :
    m.left.unop.label = 1 := by
  have h := congrArg (fun a => a.unop.label) (CostructuredArrow.w m)
  change m.left.unop.label * 1 = 1 at h
  simpa using h

/-- Forgetting a forced label-one comma arrow gives its original inclusion. -/
def commaInclusionFullyFaithful (U : Opens X) :
    (commaInclusion f hf U).FullyFaithful where
  preimage {j k} m := CostructuredArrow.homMk (homOfLE (fun y hy => by
    have h := m.left.unop.mapsTo y hy
    rw [commaInclusion_label_one f hf U m, one_smul] at h
    exact h)).op
  map_preimage m := by
    apply CostructuredArrow.ext
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    exact (commaInclusion_label_one f hf U m).symm
  preimage_map _ := CostructuredArrow.ext _ _ (Subsingleton.elim _ _)

/-- Inverse translation identifies a labelled inverse-image open with its target. -/
def preimageOpenIso (g : G) (V : Opens Y) :
    (⟨Godement.preimageOpen g V⟩ : ActionOpens G Y) ≅ ⟨V⟩ where
  hom := Godement.preimageArrow g V
  inv := ⟨g⁻¹, fun y hy => by
    change g • (g⁻¹ • y) ∈ V
    simpa using hy⟩
  hom_inv_id := ActionOpens.Hom.ext (inv_mul_cancel g)
  inv_hom_id := ActionOpens.Hom.ext (mul_inv_cancel g)

/-- Translating the target open normalizes every transport comma object. -/
instance commaInclusion_essSurj (U : Opens X) : (commaInclusion f hf U).EssSurj where
  mem_essImage j := by
    let g := j.hom.unop.label
    let V := j.left.unop.openSet
    let W := Godement.preimageOpen g V
    have hU : U ≤ (Opens.map (TopCat.ofHom f)).obj W := by
      intro x hx
      change g • f x ∈ V
      rw [← hf]
      exact j.hom.unop.mapsTo x hx
    let k : CostructuredArrow (Opens.map (TopCat.ofHom f)).op (op U) :=
      CostructuredArrow.mk (homOfLE hU).op
    refine ⟨k, ⟨CostructuredArrow.isoMk (preimageOpenIso g V).op.symm ?_⟩⟩
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    change g⁻¹ * g = 1
    exact inv_mul_cancel g

/-- The two inverse-image comma categories are equivalent. -/
instance commaInclusion_isEquivalence (U : Opens X) :
    (commaInclusion f hf U).IsEquivalence where
  faithful := (commaInclusionFullyFaithful f hf U).faithful
  full := (commaInclusionFullyFaithful f hf U).full

/-- The transport Kan-extension unit restricted to ordinary opens. -/
def restrictedUnit (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat ℂ) :
    (ActionOpens.inclusion G Y).op ⋙ F ⟶
      (Opens.map (TopCat.ofHom f)).op ⋙
        ((ActionOpens.inclusion G X).op ⋙ (DirectImage.preimage f hf).op.lan.obj F) :=
  Functor.whiskerLeft (ActionOpens.inclusion G Y).op
    ((DirectImage.preimage f hf).op.lanUnit.app F)

/-- The same transport extension is pointwise universal after forgetting labels. -/
def restrictedPointwise (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat ℂ) :
    (Functor.LeftExtension.mk _ (restrictedUnit f hf F)).IsPointwiseLeftKanExtension :=
  fun U =>
    (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((DirectImage.preimage f hf).op.lan.obj F)
      ((DirectImage.preimage f hf).op.lanUnit.app F) (op ⟨U.unop⟩)).whiskerEquivalence
        (commaInclusion f hf U.unop).asEquivalence

instance restricted_isLeftKanExtension (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat ℂ) :
    ((ActionOpens.inclusion G X).op ⋙ (DirectImage.preimage f hf).op.lan.obj F).IsLeftKanExtension
      (restrictedUnit f hf F) :=
  (restrictedPointwise f hf F).isLeftKanExtension

/-- Ordinary restriction of the actual transport left Kan extension. -/
def presheafObjectIso (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat ℂ) :
    (ActionOpens.inclusion G X).op ⋙ (DirectImage.preimage f hf).op.lan.obj F ≅
      (Opens.map (TopCat.ofHom f)).op.lan.obj ((ActionOpens.inclusion G Y).op ⋙ F) :=
  Functor.leftKanExtensionUnique _ (restrictedUnit f hf F) _
    ((Opens.map (TopCat.ofHom f)).op.lanUnit.app ((ActionOpens.inclusion G Y).op ⋙ F))

omit [ContinuousConstSMul G X] in
/-- The comparison preserves the original inverse-image unit. -/
@[reassoc (attr := simp)]
theorem restrictedUnit_presheafObjectIso_hom (F : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat ℂ) :
    restrictedUnit f hf F ≫
      Functor.whiskerLeft (Opens.map (TopCat.ofHom f)).op (presheafObjectIso f hf F).hom =
        (Opens.map (TopCat.ofHom f)).op.lanUnit.app ((ActionOpens.inclusion G Y).op ⋙ F) := by
  simp [presheafObjectIso]

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
/-- The restricted unit is natural in the original transport presheaf. -/
@[reassoc]
theorem restrictedUnit_naturality
    {F F' : (ActionOpens G Y)ᵒᵖ ⥤ ModuleCat ℂ} (k : F ⟶ F') :
    restrictedUnit f hf F ≫
      Functor.whiskerLeft (Opens.map (TopCat.ofHom f)).op
        (Functor.whiskerLeft (ActionOpens.inclusion G X).op
          ((DirectImage.preimage f hf).op.lan.map k)) =
      Functor.whiskerLeft (ActionOpens.inclusion G Y).op k ≫ restrictedUnit f hf F' := by
  apply NatTrans.ext
  funext V
  exact NatTrans.congr_app ((DirectImage.preimage f hf).op.lanUnit.naturality k).symm
    ((ActionOpens.inclusion G Y).op.obj V)

/-- Forgetting labels commutes naturally with the actual presheaf inverse image. -/
def presheafIso :
    (DirectImage.preimage f hf).op.lan ⋙ underlyingPresheaf G X (ModuleCat ℂ) ≅
      underlyingPresheaf G Y (ModuleCat ℂ) ⋙ (Opens.map (TopCat.ofHom f)).op.lan :=
  NatIso.ofComponents (presheafObjectIso f hf) (fun k => by
    apply Functor.hom_ext_of_isLeftKanExtension _ (restrictedUnit f hf _)
    change restrictedUnit f hf _ ≫ Functor.whiskerLeft (Opens.map (TopCat.ofHom f)).op
        (Functor.whiskerLeft (ActionOpens.inclusion G X).op
            ((DirectImage.preimage f hf).op.lan.map k) ≫ (presheafObjectIso f hf _).hom) =
      restrictedUnit f hf _ ≫ Functor.whiskerLeft (Opens.map (TopCat.ofHom f)).op
        ((presheafObjectIso f hf _).hom ≫ (Opens.map (TopCat.ofHom f)).op.lan.map
          (Functor.whiskerLeft (ActionOpens.inclusion G Y).op k))
    simp only [Functor.whiskerLeft_comp, ← Category.assoc]
    rw [restrictedUnit_naturality]
    rw [Category.assoc, restrictedUnit_presheafObjectIso_hom,
      restrictedUnit_presheafObjectIso_hom]
    apply NatTrans.ext
    funext V
    exact NatTrans.congr_app ((Opens.map (TopCat.ofHom f)).op.lanUnit.naturality
      (Functor.whiskerLeft (ActionOpens.inclusion G Y).op k)) V)

/-- Sheafifying the transport inverse image commutes with forgetting labels. -/
def presheafSheafIso :
    ((DirectImage.preimage f hf).op.lan ⋙
        presheafToSheaf (transportTopology G X) (ModuleCat ℂ)) ⋙
      (ActionOpens.inclusion G X).sheafPushforwardContinuous (ModuleCat ℂ)
        (Opens.grothendieckTopology X) (transportTopology G X) ≅
    underlyingPresheaf G Y (ModuleCat ℂ) ⋙
      (Opens.map (TopCat.ofHom f)).op.lan ⋙
        presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat ℂ) :=
  Functor.isoWhiskerLeft (DirectImage.preimage f hf).op.lan
      ((ActionOpens.inclusion G X).pushforwardContinuousSheafificationCompatibility
        (ModuleCat ℂ) (Opens.grothendieckTopology X) (transportTopology G X)).symm ≪≫
    Functor.isoWhiskerRight (presheafIso f hf)
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat ℂ))

/-- Forgetting equivariance commutes with inverse image on the two actual sites. -/
def siteIso :
    Functor.sheafPullbackConstruction.sheafPullback (DirectImage.preimage f hf)
        (ModuleCat ℂ) (transportTopology G Y) (transportTopology G X) ⋙
      (ActionOpens.inclusion G X).sheafPushforwardContinuous (ModuleCat ℂ)
        (Opens.grothendieckTopology X) (transportTopology G X) ≅
    (ActionOpens.inclusion G Y).sheafPushforwardContinuous (ModuleCat ℂ)
        (Opens.grothendieckTopology Y) (transportTopology G Y) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (Opens.map (TopCat.ofHom f))
        (ModuleCat ℂ) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  Functor.isoWhiskerLeft (sheafToPresheaf (transportTopology G Y) (ModuleCat ℂ))
    (presheafSheafIso f hf)

/-- The underlying ordinary sheaf of the actual equivariant inverse image is
the ordinary sheaf inverse image of the original underlying sheaf. -/
def toSheafIso :
    actionInverseImage f hf ⋙ toSheaf G X (ModuleCat ℂ) ≅
      toSheaf G Y (ModuleCat ℂ) ⋙ TopCat.Sheaf.pullback (ModuleCat ℂ) (TopCat.ofHom f) :=
  Functor.isoWhiskerLeft (sheafEquivalence G Y (ModuleCat ℂ)).functor (siteIso f hf) ≪≫
    Functor.isoWhiskerLeft (toSheaf G Y (ModuleCat ℂ))
      (TopCat.Sheaf.pullbackIso (ModuleCat ℂ) (TopCat.ofHom f)).symm

end Langlands.Sheaf.Renard.SectionActions.InverseImageComparison
