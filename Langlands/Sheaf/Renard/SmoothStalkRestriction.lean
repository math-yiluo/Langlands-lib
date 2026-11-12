import Langlands.Sheaf.Renard.StalkActions
import Langlands.Sheaf.CompactGerms
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Smooth subgroup and point restriction in Renard III.3.2

The compact global germ map is an equivariant surjection onto the original
fixed stalk. Smoothness therefore transfers from all compact sections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions

open CategoryTheory Opposite
open Langlands.Sheaf.Equivariant

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Restricting the group action on all compact sections preserves smoothness. -/
theorem isSmoothAction_subgroupRestriction (Q : Subgroup G)
    (F : ActionSheaf G X) (hF : IsSmoothAction F) :
    IsSmoothAction ((subgroupRestriction Q).obj F) := by
  change Langlands.IsSmooth ((compactRepresentation F).comp Q.subtype)
  exact Langlands.isSmooth_comp Q.subtype continuous_subtype_val hF

/-- Smooth subgroup restriction retains the original action sheaf and its maps. -/
def smoothSubgroupRestriction (Q : Subgroup G) :
    SmoothActionSheaf G X ⥤ SmoothActionSheaf Q X :=
  (smoothActionProperty Q X).lift
    (smoothActionInclusion G X ⋙ subgroupRestriction Q)
    (fun F => isSmoothAction_subgroupRestriction Q F.obj F.property)

variable (Q : Subgroup G) (x : X) (hfix : ∀ q : Q, (q : G) • x = x)

/-- The original compact global germ map intertwines subgroup and stalk actions. -/
def fixedStalkCompactGerm (F : ActionSheaf G X) :
    Representation.IntertwiningMap ((compactRepresentation F).comp Q.subtype)
      ((fixedStalkFunctor Q x hfix).obj F).ρ where
  toLinearMap := Langlands.Sheaf.CompactGerms.germ (underlying F) x
  isIntertwining' q := by
    ext s
    exact (congrArg (fun f => f.hom s.val)
      (Godement.germ_stalkPull_arrow F.obj
        (ActionOpens.sectionArrow (q : G)) x x (hfix q⁻¹) trivial)).symm

/-- The intertwiner is exactly the original global germ on compact sections. -/
theorem fixedStalkCompactGerm_apply (F : ActionSheaf G X)
    (s : Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj)) :
    fixedStalkCompactGerm Q x hfix F s =
      (CompactSections.ordinary F.obj).Γgerm x s.val := rfl

/-- Compact zero extension makes the actual equivariant germ map surjective. -/
theorem fixedStalkCompactGerm_surjective (F : ActionSheaf G X)
    (hX : Langlands.Topology.IsLocallyProfinite X) :
    Function.Surjective (fixedStalkCompactGerm Q x hfix F) :=
  Langlands.Sheaf.CompactGerms.germ_surjective (underlying F) hX x

/-- Renard smoothness of all compact sections gives smoothness of the original stalk. -/
theorem isSmooth_fixedStalk (F : ActionSheaf G X)
    (hX : Langlands.Topology.IsLocallyProfinite X) (hF : IsSmoothAction F) :
    Langlands.IsSmooth ((fixedStalkFunctor Q x hfix).obj F).ρ :=
  Langlands.isSmooth_of_surjective (fixedStalkCompactGerm Q x hfix F)
    (fixedStalkCompactGerm_surjective Q x hfix F hX)
    (Langlands.isSmooth_comp Q.subtype continuous_subtype_val hF)

/-- Renard's point restriction into smooth representations, on the actual stalk. -/
def smoothFixedStalkFunctor (hX : Langlands.Topology.IsLocallyProfinite X) :
    SmoothActionSheaf G X ⥤ Langlands.SmoothRep.{0, uG, 0} ℂ Q :=
  (Langlands.smoothRepProperty ℂ Q).lift
    (smoothActionInclusion G X ⋙ fixedStalkFunctor Q x hfix)
    (fun F => isSmooth_fixedStalk Q x hfix F.obj hX F.property)

/-- Forgetting smoothness recovers the published original-stalk functor. -/
def smoothFixedStalkToRepIso (hX : Langlands.Topology.IsLocallyProfinite X) :
    smoothFixedStalkFunctor Q x hfix hX ⋙ Langlands.SmoothRep.toRep ≅
      smoothActionInclusion G X ⋙ fixedStalkFunctor Q x hfix :=
  (Langlands.smoothRepProperty ℂ Q).liftCompιIso _ _

/-- The smooth point-restriction action is the original stalk action. -/
theorem smoothFixedStalk_representation (hX : Langlands.Topology.IsLocallyProfinite X)
    (F : SmoothActionSheaf G X) :
    ((smoothFixedStalkFunctor Q x hfix hX).obj F).representation =
      ((fixedStalkFunctor Q x hfix).obj F.obj).ρ := rfl

/-- The smooth point-restriction maps are the original induced stalk maps. -/
theorem smoothFixedStalk_map (hX : Langlands.Topology.IsLocallyProfinite X)
    {F F' : SmoothActionSheaf G X} (f : F ⟶ F') :
    (Langlands.SmoothRep.hom ((smoothFixedStalkFunctor Q x hfix hX).map f)).toLinearMap =
      ((TopCat.Presheaf.stalkFunctor (X := TopCat.of X) (ModuleCat.{0} ℂ) x).map
        ((underlyingPresheaf G X (ModuleCat ℂ)).map f.hom.hom)).hom := rfl

end Langlands.Sheaf.Renard.SectionActions
