import Langlands.Sheaf.Renard.InverseImageComparison
import Langlands.Sheaf.Renard.SectionActions
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.RepresentationTheory.Coinvariants

/-!
# Original invariant fibres and their equivariant sheaf restrictions

The base is the literal subtype q(x)=y. Its inherited group action,
continuous inclusion and actual inverse-image sheaf define the compact
fibre representation and its original coinvariant vector space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.InvariantFibres

open CategoryTheory
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions

variable {G X Y : Type} [Group G] [TopologicalSpace G]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [ContinuousSMul G X]
variable (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x) (y : Y)

/-- The original topological fibre, with its literal subtype topology. -/
abbrev Fibre := {x : X // q x = y}

/-- Invariance of q restricts the actual group action to its actual fibre. -/
@[instance_reducible]
def fibreAction : MulAction G (Fibre q y) where
  smul g x := ⟨g • x.val, (hq g x.val).trans x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g k x := Subtype.ext (mul_smul g k x.val)

/-- Joint continuity is inherited from the original action, through the subtype inclusion. -/
theorem fibreContinuousSMul :
    letI := fibreAction q hq y
    ContinuousSMul G (Fibre q y) := by
  let := fibreAction q hq y
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

/-- The actual inclusion of the original fibre. -/
def inclusion : C(Fibre q y, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The original fibre is closed when the target is Hausdorff. -/
theorem fibre_closed [T2Space Y] : IsClosed {x : X | q x = y} :=
  isClosed_singleton.preimage q.continuous

/-- The fibre retains the actual Hausdorff compact-open basis of the source. -/
theorem fibre_isLocallyProfinite
    (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) :
    Langlands.Topology.IsLocallyProfinite (Fibre q y) := by
  let := hY.t2Space
  exact Langlands.Topology.LocallyProfiniteProof.locallyClosedSubspaces X hX
    {x : X | q x = y} (fibre_closed q y).isLocallyClosed

/-- Restrict the original action sheaf by its actual equivariant inverse image. -/
def restriction :
    letI := fibreAction q hq y
    ActionSheaf G X ⥤ ActionSheaf G (Fibre q y) :=
  letI := fibreAction q hq y
  letI := fibreContinuousSMul q hq y
  actionInverseImage (inclusion q y) (fun _ _ => rfl)

/-- Forgetting the restricted action gives the original ordinary sheaf inverse image. -/
def restrictionToSheafIso :
    letI := fibreAction q hq y
    restriction q hq y ⋙ toSheaf G (Fibre q y) (ModuleCat.{0} ℂ) ≅
      toSheaf G X (ModuleCat.{0} ℂ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (TopCat.ofHom (inclusion q y)) :=
  letI := fibreAction q hq y
  letI := fibreContinuousSMul q hq y
  InverseImageComparison.toSheafIso (inclusion q y) (fun _ _ => rfl)

/-- The original compact-section representation of the actual fibre restriction. -/
def compactSections : ActionSheaf G X ⥤ Rep.{0} ℂ G :=
  letI := fibreAction q hq y
  letI := fibreContinuousSMul q hq y
  restriction q hq y ⋙ CompactSections.functor ℂ G (Fibre q y)

/-- The existing functor of literal representation coinvariants and induced maps. -/
abbrev representationCoinvariants : Rep.{0} ℂ G ⥤ ModuleCat.{0} ℂ :=
  Rep.coinvariantsFunctor ℂ G

/-- The actual compact-fibre coinvariant vector spaces, naturally in the original sheaf. -/
def coinvariants : ActionSheaf G X ⥤ ModuleCat.{0} ℂ :=
  compactSections q hq y ⋙ representationCoinvariants

end Langlands.Sheaf.Renard.InvariantFibres
