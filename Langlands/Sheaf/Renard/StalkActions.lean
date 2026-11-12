import Langlands.Sheaf.Renard.SectionActions
import Langlands.Sheaf.Equivariant.Godement.Stalks

/-!
# Subgroup restriction and the action on a fixed stalk

These constructions use the published transport category and the actual
neighborhood-colimit stalk maps. They are the underlying algebraic functors
needed for Renard's restriction at a point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions

open CategoryTheory Opposite
open Langlands.Sheaf.Equivariant

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type} [TopologicalSpace X] [MulAction G X]

/-- Retain the same opens and restrict the transport labels to a subgroup. -/
def subgroupOpens (Q : Subgroup G) : ActionOpens Q X ⥤ ActionOpens G X where
  obj U := ⟨U.openSet⟩
  map f := ⟨f.label, f.mapsTo⟩
  map_id _ := ActionOpens.Hom.ext rfl
  map_comp _ _ := ActionOpens.Hom.ext rfl

/-- Restrict an equivariant sheaf's group action, leaving its ordinary sheaf unchanged. -/
def subgroupRestriction (Q : Subgroup G) : ActionSheaf G X ⥤ ActionSheaf Q X where
  obj F := ⟨(subgroupOpens Q).op ⋙ F.obj, by
    change ((underlyingPresheaf G X (ModuleCat ℂ)).obj F.obj).IsSheaf
    exact F.property⟩
  map f := ObjectProperty.homMk (Functor.whiskerLeft (subgroupOpens Q).op f.hom)

variable [ContinuousSMul G X]

/-- Forward transport of the actual stalk, using the inverse-labelled pullback. -/
def stalkTransport (F : ActionSheaf G X) (g : G) (x : X) :
    (CompactSections.ordinary F.obj).stalk x ≅
      (CompactSections.ordinary F.obj).stalk (g • x) :=
  Godement.stalkPullIso F.obj g⁻¹ (g • x) x (inv_smul_smul g x)

variable (Q : Subgroup G) (x : X) (hfix : ∀ q : Q, (q : G) • x = x)

/-- The actual action of a point-fixing subgroup on the neighborhood-colimit stalk. -/
def fixedStalkAction (F : ActionSheaf G X) : Action (ModuleCat ℂ) Q where
  V := (CompactSections.ordinary F.obj).stalk x
  ρ :=
    { toFun q := Godement.stalkPull F.obj (q : G)⁻¹ x x (hfix q⁻¹)
      map_one' := by
        simp
      map_mul' g h := by
        change Godement.stalkPull F.obj ((g * h : Q) : G)⁻¹ x x _ =
          Godement.stalkPull F.obj (h : G)⁻¹ x x _ ≫
            Godement.stalkPull F.obj (g : G)⁻¹ x x _
        simpa only [Subgroup.coe_mul, mul_inv_rev] using
          Godement.stalkPull_mul F.obj (g : G)⁻¹ (h : G)⁻¹ x x x
            (hfix g⁻¹) (hfix h⁻¹) }

/-- Stalk evaluation, with its point-fixing subgroup action, is functorial in sheaves. -/
def fixedStalkActions : ActionSheaf G X ⥤ Action (ModuleCat ℂ) Q where
  obj F := fixedStalkAction Q x hfix F
  map f :=
    { hom := (TopCat.Presheaf.stalkFunctor (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map
        ((underlyingPresheaf G X (ModuleCat ℂ)).map f.hom)
      comm q := Godement.stalkPull_naturality f.hom (q : G)⁻¹ x x (hfix q⁻¹) }
  map_id F := by
    apply Action.Hom.ext
    simp [fixedStalkAction]
  map_comp f g := by
    apply Action.Hom.ext
    simp

/-- The underlying representation-valued point restriction, before a smoothness assertion. -/
def fixedStalkFunctor : ActionSheaf G X ⥤ Rep ℂ Q :=
  fixedStalkActions Q x hfix ⋙ Rep.ActionToRep ℂ Q

/-- The forward action on a stalk is literally the published inverse-labelled pullback. -/
theorem fixedStalkAction_apply (F : ActionSheaf G X) (q : Q) :
    (fixedStalkAction Q x hfix F).ρ q =
      Godement.stalkPull F.obj (q : G)⁻¹ x x (hfix q⁻¹) := rfl

end Langlands.Sheaf.Renard.SectionActions
