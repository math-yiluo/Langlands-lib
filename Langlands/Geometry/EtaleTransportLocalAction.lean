import Langlands.Geometry.EtaleTransportSections
import Mathlib.RepresentationTheory.Rep.Res

/-! # Subgroup actions on actual small-etale objects and their sections -/

noncomputable section

universe u w uA vA uR uM

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ) (H : Subgroup G)

/-- A small-etale object with a specified subgroup action lifting the base action. -/
structure LocalAction where
  object : Object ρ
  action : H →* (Aut object.etale.left)ᵐᵒᵖ
  equivariant (h : H) :
    (aut action h).hom ≫ object.etale.hom =
      object.etale.hom ≫ (aut ρ (h : G)).hom

namespace LocalAction

variable {ρ H}

/-- Equivariant ordinary small-etale maps between objects with lifted actions. -/
@[ext]
structure Hom (U V : LocalAction ρ H) where
  hom : U.object.etale ⟶ V.object.etale
  comm (h : H) :
    (aut U.action h).hom ≫ hom.left = hom.left ≫ (aut V.action h).hom

instance : Category (LocalAction ρ H) where
  Hom := Hom
  id U :=
    { hom := 𝟙 U.object.etale
      comm h := by
        change (aut U.action h).hom ≫ 𝟙 _ = 𝟙 _ ≫ (aut U.action h).hom
        rw [Category.comp_id, Category.id_comp] }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm h := by
        change (aut _ h).hom ≫ (f.hom.left ≫ g.hom.left) =
          (f.hom.left ≫ g.hom.left) ≫ (aut _ h).hom
        rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc] }
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

/-- Forget the lifted action, retaining the actual small-etale scheme and maps. -/
def forget : LocalAction ρ H ⥤ Y.Etale where
  obj U := U.object.etale
  map f := f.hom

instance : (forget (ρ := ρ) (H := H)).Faithful where
  map_injective := Hom.ext

/-- The subgroup element gives its labelled automorphism of the transport object. -/
def transport (U : LocalAction ρ H) (h : H) : U.object ⟶ U.object where
  label := h
  left := (aut U.action h).hom
  w := U.equivariant h

@[simp] theorem transport_label (U : LocalAction ρ H) (h : H) :
    (U.transport h).label = (h : G) := rfl

@[simp] theorem transport_left (U : LocalAction ρ H) (h : H) :
    (U.transport h).left = (aut U.action h).hom := rfl

@[simp] theorem transport_one (U : LocalAction ρ H) :
    U.transport 1 = 𝟙 U.object :=
  Object.Hom.ext rfl (by simp [aut_one])

theorem transport_mul (U : LocalAction ρ H) (h k : H) :
    U.transport (h * k) = U.transport h ≫ U.transport k :=
  Object.Hom.ext rfl (by simp [aut_mul])

/-- The inverse transport arrow is supplied by the inverse subgroup element. -/
def transportIso (U : LocalAction ρ H) (h : H) : U.object ≅ U.object where
  hom := U.transport h
  inv := U.transport h⁻¹
  hom_inv_id := by rw [← transport_mul, mul_inv_cancel, transport_one]
  inv_hom_id := by rw [← transport_mul, inv_mul_cancel, transport_one]

/-- The ordinary map of an equivariant arrow commutes with labelled transport. -/
theorem Hom.comm_transport {U V : LocalAction ρ H} (f : U ⟶ V) (h : H) :
    U.transport h ≫ (inclusion ρ).map f.hom =
      (inclusion ρ).map f.hom ≫ V.transport h :=
  Object.Hom.ext (by simp) (f.comm h)

variable (ρ H)

/-- The whole scheme carries the restriction of its given geometric action. -/
def whole : LocalAction ρ H where
  object := EtaleTransport.whole ρ
  action := ρ.comp H.subtype
  equivariant h := by
    change (aut ρ (h : G)).hom ≫ 𝟙 Y = 𝟙 Y ≫ (aut ρ (h : G)).hom
    simp

@[simp] theorem whole_transport (h : H) :
    (whole ρ H).transport h = wholeMap ρ (h : G) := rfl

variable {ρ H} {K : Subgroup G}

/-- Restrict a genuine lifted action to a smaller subgroup. -/
def restrict (hKH : K ≤ H) : LocalAction ρ H ⥤ LocalAction ρ K where
  obj U :=
    { object := U.object
      action := U.action.comp (Subgroup.inclusion hKH)
      equivariant k := U.equivariant (Subgroup.inclusion hKH k) }
  map f :=
    { hom := f.hom
      comm k := f.comm (Subgroup.inclusion hKH k) }

@[simp] theorem restrict_obj_transport (hKH : K ≤ H) (U : LocalAction ρ H) (k : K) :
    ((restrict hKH).obj U).transport k = U.transport (Subgroup.inclusion hKH k) := rfl

variable (A : Type uA) [Category.{vA} A]

/-- Sections of an actual transport sheaf, acted on by the lifted subgroup. -/
def sectionAction (U : LocalAction ρ H) : Sheaf ρ A ⥤ Action A H where
  obj F :=
    { V := F.obj.obj (op U.object)
      ρ :=
        { toFun h := F.obj.map (U.transport h).op
          map_one' := by rw [transport_one, op_id, F.obj.map_id]; rfl
          map_mul' h k := by rw [transport_mul, op_comp, F.obj.map_comp]; rfl } }
  map f :=
    { hom := f.hom.app (op U.object)
      comm h := f.hom.naturality (U.transport h).op }

@[simp] theorem sectionAction_obj_ρ (U : LocalAction ρ H) (F : Sheaf ρ A) (h : H) :
    ((sectionAction A U).obj F).ρ h = F.obj.map (U.transport h).op := rfl

/-- Forgetting the subgroup action gives actual evaluation on the small-etale object. -/
def sectionActionForgetIso (U : LocalAction ρ H) :
    sectionAction A U ⋙ Action.forget A H ≅ evaluation ρ A U.object :=
  Iso.refl _

/-- Equivariant geometric restriction is natural in the transport sheaf. -/
def sectionRestriction {U V : LocalAction ρ H} (f : U ⟶ V) :
    sectionAction A V ⟶ sectionAction A U where
  app F :=
    { hom := F.obj.map ((inclusion ρ).map f.hom).op
      comm h := by
        change F.obj.map (V.transport h).op ≫
            F.obj.map ((inclusion ρ).map f.hom).op =
          F.obj.map ((inclusion ρ).map f.hom).op ≫ F.obj.map (U.transport h).op
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        exact congrArg (fun k => F.obj.map k.op) (f.comm_transport h).symm }
  naturality {F E} f := by
    apply Action.Hom.ext
    exact (f.hom.naturality _).symm

/-- The local section action is contravariantly functorial in equivariant etale objects. -/
def sectionDiagram : (LocalAction ρ H)ᵒᵖ ⥤ (Sheaf ρ A ⥤ Action A H) where
  obj U := sectionAction A U.unop
  map f := sectionRestriction A f.unop
  map_id U := by
    apply NatTrans.ext
    funext F
    apply Action.Hom.ext
    change F.obj.map ((inclusion ρ).map (𝟙 U.unop.object.etale)).op = 𝟙 _
    rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply NatTrans.ext
    funext F
    apply Action.Hom.ext
    change F.obj.map ((inclusion ρ).map (g.unop.hom ≫ f.unop.hom)).op = _
    rw [CategoryTheory.Functor.map_comp, op_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- On the whole scheme this is the existing global section action restricted to the subgroup. -/
def wholeSectionIso :
    sectionAction A (whole ρ H) ≅
      EtaleTransport.sectionAction ρ A ⋙ Action.res A H.subtype :=
  Iso.refl _

/-- Restricting a lifted action agrees with restricting its section action. -/
def restrictSectionIso (hKH : K ≤ H) (U : LocalAction ρ H) :
    sectionAction A ((restrict hKH).obj U) ≅
      sectionAction A U ⋙ Action.res A (Subgroup.inclusion hKH) :=
  Iso.refl _

variable (R : Type uR) [CommRing R]

/-- The actual module of sections with its lifted-subgroup representation. -/
def sectionRepresentation (U : LocalAction ρ H) :
    ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R H :=
  sectionAction (ModuleCat.{uM} R) U ⋙ Rep.ActionToRep R H

instance sectionRepresentation_additive (U : LocalAction ρ H) :
    (sectionRepresentation R U : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _).Additive where
  map_add {F E} f g := by ext s; rfl

/-- Forgetting the representation retains actual local sections. -/
def sectionRepresentationForgetIso (U : LocalAction ρ H) :
    sectionRepresentation R U ⋙ forget₂ (Rep.{uM} R H) (ModuleCat.{uM} R) ≅
      evaluation ρ (ModuleCat.{uM} R) U.object :=
  Iso.refl _

instance sectionRepresentation_preservesFiniteLimits (U : LocalAction ρ H) :
    PreservesFiniteLimits
      (sectionRepresentation R U : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) := by
  have : PreservesFiniteLimits
      (sectionRepresentation R U ⋙ forget₂ (Rep.{uM} R H) (ModuleCat.{uM} R)) :=
    preservesFiniteLimits_of_natIso (sectionRepresentationForgetIso R U).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (Rep.{uM} R H) (ModuleCat.{uM} R))

/-- Geometric restriction is a natural intertwiner of the actual local representations. -/
def representationRestriction {U V : LocalAction ρ H} (f : U ⟶ V) :
    sectionRepresentation R V ⟶
      (sectionRepresentation R U : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) :=
  Functor.whiskerRight (sectionRestriction (ModuleCat.{uM} R) f) (Rep.ActionToRep R H)

@[simp] theorem representationRestriction_app_hom {U V : LocalAction ρ H}
    (f : U ⟶ V) (F : ModuleSheaf.{u, w, uR, uM} ρ R) :
    ((representationRestriction R f).app F).hom.toLinearMap =
      (F.obj.map ((inclusion ρ).map f.hom).op).hom := rfl

/-- The whole-object representation is the existing global section representation
restricted to the specified subgroup. -/
def wholeRepresentationIso :
    sectionRepresentation R (whole ρ H) ≅
      (EtaleTransport.sectionRepresentation ρ R :
        ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G) ⋙ Rep.resFunctor H.subtype :=
  Iso.refl _

end LocalAction

end Langlands.Geometry.EtaleTransport
