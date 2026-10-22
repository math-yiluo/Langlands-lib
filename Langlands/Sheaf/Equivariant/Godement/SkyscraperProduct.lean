import Langlands.Sheaf.Equivariant.Godement.Zero
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Limits

/-!
# The ordinary skyscraper-product identification

Forgetting equivariance, the constructed sheaf of stalk families satisfies
the universal property of the product of the actual skyscraper sheaves.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u uG

attribute [local instance] Classical.propDecidable

variable {R : Type u} [CommRing R]
variable {G : Type uG} [Group G] {X : Type u} [TopologicalSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

/-- Read a skyscraper section on an open containing its point. -/
def skyscraperRead (x : X) (M : ModuleCat.{u} R) (U : Opens X) (hx : x ∈ U) :
    (skyscraperPresheaf (X := TopCat.of X) x M).obj (op U) ⟶ M :=
  eqToHom (ite_eq_left hx)

instance (x : X) (M : ModuleCat.{u} R) (U : Opens X) (hx : x ∈ U) :
    IsIso (skyscraperRead x M U hx) := by
  dsimp [skyscraperRead]
  infer_instance

@[reassoc]
theorem skyscraper_map_read (x : X) (M : ModuleCat.{u} R)
    {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) :
    (skyscraperPresheaf (X := TopCat.of X) x M).map i.op ≫
        skyscraperRead x M U hx =
      skyscraperRead x M V (i.le hx) := by
  simp [skyscraperRead, skyscraperPresheaf_map, hx]

variable (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)

/-- Evaluation of a stalk family at a point of its open. -/
def familyEvaluation (U : Opens X) (x : X) (hx : x ∈ U) :
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (zeroPresheaf F)).obj (op U) ⟶ ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x :=
  ModuleCat.ofHom (LinearMap.proj (⟨x, hx⟩ : U))

@[reassoc]
theorem familyEvaluation_restrict {U V : Opens X} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) :
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (zeroPresheaf F)).map i.op ≫ familyEvaluation F U x hx =
      familyEvaluation F V x (i.le hx) := by
  ext s
  exact stalkPull_one_section F V s x _ (i.le hx) _ rfl

/-- The pointwise component of the projection to one ordinary skyscraper. -/
def skyscraperProjectionApp (x : X) (U : Opens X) :
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (zeroPresheaf F)).obj (op U) ⟶
      (skyscraperPresheaf (X := TopCat.of X) x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x)).obj
        (op U) :=
  if hx : x ∈ U then
    familyEvaluation F U x hx ≫ inv (skyscraperRead x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) U hx)
  else
    (isTerminalSkyscraperSheafObjObjOfNotMem
      (A := ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) hx).from _

@[reassoc (attr := simp)]
theorem skyscraperProjectionApp_read (x : X) (U : Opens X) (hx : x ∈ U) :
    skyscraperProjectionApp F x U ≫ skyscraperRead x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) U hx =
      familyEvaluation F U x hx := by
  simp [skyscraperProjectionApp, hx]

/-- Projection to the actual skyscraper sheaf with coefficient the given stalk. -/
def skyscraperProjection (x : X) :
    (toSheaf G X (ModuleCat.{u} R)).obj (zeroSheaf F) ⟶
      skyscraperSheaf (X := TopCat.of X) x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) :=
  ObjectProperty.homMk
    { app U := skyscraperProjectionApp F x U.unop
      naturality U V i := by
        change ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (zeroPresheaf F)).map i ≫ skyscraperProjectionApp F x V.unop =
          skyscraperProjectionApp F x U.unop ≫
            (skyscraperPresheaf (X := TopCat.of X) x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x)).map i.unop.op
        by_cases hx : x ∈ V.unop
        · apply (cancel_mono (skyscraperRead x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) V.unop hx)).1
          rw [Category.assoc, skyscraperProjectionApp_read]
          rw [Category.assoc, skyscraper_map_read, skyscraperProjectionApp_read]
          exact familyEvaluation_restrict F i.unop x hx
        · exact (isTerminalSkyscraperSheafObjObjOfNotMem
            (A := ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) hx).hom_ext _ _ }

/-- The explicit cone from the sheaf of stalk families to all skyscrapers. -/
def skyscraperFan :
    Fan (fun x : X =>
      skyscraperSheaf (X := TopCat.of X) x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x)) :=
  Fan.mk ((toSheaf G X (ModuleCat.{u} R)).obj (zeroSheaf F))
    (skyscraperProjection F)

/-- The universal map assembles the point components of a skyscraper cone. -/
def skyscraperFanLift (c : Fan (fun x : X =>
    skyscraperSheaf (X := TopCat.of X) x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x))) :
    c.pt ⟶ (skyscraperFan F).pt :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun s x :=
            skyscraperRead x.1 (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x.1) U.unop x.2
              ((c.π.app ⟨x.1⟩).hom.app U s)
          map_add' s t := by
            ext x
            simp only [map_add]
            rfl
          map_smul' r s := by
            ext x
            simp only [map_smul]
            rfl }
      naturality U V i := by
        ext s
        funext x
        let t : ∀ z : U.unop, ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk z.1 := fun z =>
          skyscraperRead z.1 (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk z.1) U.unop z.2
            ((c.π.app ⟨z.1⟩).hom.app U s)
        change (c.pt.obj.map i ≫ (c.π.app ⟨x.1⟩).hom.app V ≫
            skyscraperRead x.1 (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x.1) V.unop x.2) s =
          stalkPull F 1 x.1 ((1 : G) • x.1) rfl (t ⟨_, _⟩)
        rw [stalkPull_one_section F U.unop t x.1 _ (i.unop.le x.2) _ rfl]
        have hn := (c.π.app ⟨x.1⟩).hom.naturality i
        change c.pt.obj.map i ≫ (c.π.app ⟨x.1⟩).hom.app V =
          (c.π.app ⟨x.1⟩).hom.app U ≫
            (skyscraperPresheaf (X := TopCat.of X) x.1 (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x.1)).map
              i.unop.op at hn
        rw [← Category.assoc, hn, Category.assoc, skyscraper_map_read]
        rfl }

/-- The ordinary skyscraper-product universal property is proved, not assumed. -/
def skyscraperFanIsLimit : IsLimit (skyscraperFan F) where
  lift := skyscraperFanLift F
  fac c j := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    by_cases hx : j.as ∈ U.unop
    · apply (cancel_mono (skyscraperRead j.as (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk j.as) U.unop hx)).1
      change (skyscraperFanLift F c).hom.app U ≫ skyscraperProjectionApp F j.as U.unop ≫
          skyscraperRead j.as (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk j.as) U.unop hx = _
      rw [skyscraperProjectionApp_read]
      rfl
    · exact (isTerminalSkyscraperSheafObjObjOfNotMem
        (A := ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk j.as) hx).hom_ext _ _
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    ext U s
    funext x
    have h := congrArg (fun a => a.hom.app U ≫
      skyscraperRead x.1 (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x.1) U.unop x.2) (hm ⟨x.1⟩)
    change (m.hom.app U ≫ skyscraperProjectionApp F x.1 U.unop) ≫ _ = _ at h
    rw [Category.assoc, skyscraperProjectionApp_read] at h
    exact congrArg (fun a => a s) h

/-- Canonical identification with the categorical product of ordinary skyscrapers. -/
def skyscraperProductIso :
    (toSheaf G X (ModuleCat.{u} R)).obj (zeroSheaf F) ≅
      ∏ᶜ (fun x : X =>
        skyscraperSheaf (X := TopCat.of X) x (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x)) :=
  (skyscraperFanIsLimit F).conePointUniqueUpToIso (limit.isLimit _)

end Langlands.Sheaf.Equivariant.Godement
