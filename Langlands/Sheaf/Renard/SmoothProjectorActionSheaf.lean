import Langlands.Sheaf.Renard.ProjectorActionSheaf
import Langlands.Sheaf.Renard.CompactSectionActions
import Langlands.Sheaf.Renard.LocalSmoothComparison

/-!
# Smoothness of the original equivariant projector sheaf

Local sections on compact opens come from original module vectors.
Their original smooth stabilizers give local smoothness, hence smoothness
of every compact section, without assuming a module comparison isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SmoothProjectorActionSheaf

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.ProjectorBasisSheaf
open Langlands.Sheaf.Renard.ProjectorActionSheaf

universe uG

variable {G : Type uG} [Group G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)
variable (M : CompatibleTestAction.{uG, 0, 0} G X)

/-- Original-vector sections have the actual inverse-labelled transport formula. -/
theorem familyPull_originalFamily {U V : ActionOpens G X} (f : U ⟶ V)
    (m : M.module.obj) :
    familyPull hX M f (ProjectorVectorSheaf.originalFamily hX V.openSet m) =
      ProjectorVectorSheaf.originalFamily hX U.openSet (M.action f.label⁻¹ m) := by
  apply BasisAllOpen.families_ext
  intro W
  apply Subtype.ext
  change M.action f.label⁻¹ (test hX (translateCompact hX f.label W.val) • m) =
    test hX W.val • M.action f.label⁻¹ m
  rw [M.compatible, test_inverse_translate]

/-- The actual original global section assignment intertwines the group operators. -/
theorem global_originalFamily (g : G) (m : M.module.obj) :
    SectionActions.globalRepresentation (sheaf hX M) g
        (ProjectorVectorSheaf.originalFamily hX ⊤ m) =
      ProjectorVectorSheaf.originalFamily hX ⊤ (M.action g m) := by
  change familyPull hX M (ActionOpens.sectionArrow g)
    (ProjectorVectorSheaf.originalFamily hX ⊤ m) = _
  erw [familyPull_originalFamily]
  simp only [ActionOpens.sectionArrow, inv_inv]
  rfl

/-- Restriction of an original-vector section keeps the same original vector. -/
theorem restrict_originalFamily (W : ActionOpens G X) (m : M.module.obj) :
    ((transportPresheaf hX M).map
      (ActionOpens.inclusionHom (U := W) le_top).op).hom
      (ProjectorVectorSheaf.originalFamily hX ⊤ m) =
        ProjectorVectorSheaf.originalFamily hX W.openSet m := by
  let := M.complexModule
  change familyPull hX M (ActionOpens.inclusionHom (U := W) le_top)
    (ProjectorVectorSheaf.originalFamily hX ⊤ m) = _
  rw [familyPull_originalFamily]
  change ProjectorVectorSheaf.originalFamily hX W.openSet (M.action (1 : G)⁻¹ m) = _
  simp

/-- Every section restricted to a compact open is its literal original-vector section. -/
theorem restrict_family_eq_original {U : ActionOpens G X} (W : CompactOpen hX)
    (hWU : W.obj ≤ U.openSet)
    (s : ProjectorVectorSheaf.familySpace hX M.module.property U.openSet) :
    ((transportPresheaf hX M).map
      (ActionOpens.inclusionHom (U := ⟨W.obj⟩) hWU).op).hom s =
      ProjectorVectorSheaf.originalFamily hX W.obj (s.val ⟨W, hWU⟩).val := by
  change familyPull hX M ((ActionOpens.inclusion G X).map (homOfLE hWU)) s = _
  erw [familyPull_inclusion]
  apply BasisAllOpen.families_ext
  intro T
  apply Subtype.ext
  exact (congrArg Subtype.val
    (s.property ⟨W, hWU⟩ ⟨T.val, T.property.trans hWU⟩ T.property)).symm

section Smooth

variable [TopologicalSpace G] [HasStableNeighbourhoods G X]

/-- Smooth original module vectors give local smoothness on all original sections. -/
theorem isSmoothSheaf
    (hM : letI := M.complexModule; Langlands.IsSmooth M.action) :
    IsSmoothSheaf ℂ G X (sheaf hX M) := by
  let := M.complexModule
  intro U s x hx
  obtain ⟨W, hxW, hWU⟩ := (compactOpenBasis hX).exists_subset U.openSet hx
  let m : M.module.obj := (s.val ⟨W, hWU⟩).val
  let t := ProjectorVectorSheaf.originalFamily hX (⊤ : Opens X) m
  obtain ⟨K, hK⟩ := hM m
  have hfix : ∀ k : (K : Subgroup G),
      SectionActions.globalRepresentation (sheaf hX M) k t = t := by
    intro k
    change SectionActions.globalRepresentation (sheaf hX M) k
      (ProjectorVectorSheaf.originalFamily hX ⊤ m) = _
    have hk : M.action (k : G) m = m :=
      (Representation.mem_invariants _ _).1 hK k
    erw [global_originalFamily]
    exact congrArg (ProjectorVectorSheaf.originalFamily hX ⊤) hk
  have ht := SectionActions.isLocallyFixedAt_of_globalFixed (sheaf hX M) t K hfix
    (⟨W.obj⟩ : ActionOpens G X) x hxW
  have he : ((transportPresheaf hX M).map
        (ActionOpens.inclusionHom (U := ⟨W.obj⟩) le_top).op).hom t =
      ((transportPresheaf hX M).map
        (ActionOpens.inclusionHom (U := ⟨W.obj⟩) hWU).op).hom s := by
    exact (restrict_originalFamily hX M ⟨W.obj⟩ m).trans
      (restrict_family_eq_original hX M W hWU s).symm
  erw [he] at ht
  exact IsLocallyFixedAt.of_restrict ℂ hWU ht

end Smooth

section RenardSmooth

variable [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G X]

/-- All compact sections are smooth, by the published local-to-compact implication. -/
theorem isSmoothAction (hG : Langlands.Topology.IsLocallyProfinite G)
    (hM : letI := M.complexModule; Langlands.IsSmooth M.action) :
    SectionActions.IsSmoothAction (sheaf hX M) := by
  let := SectionActions.hasStableNeighbourhoods_of_locallyProfinite (X := X) hG
  exact CompactSections.isSmooth_representation_of_isSmoothSheaf
    (isSmoothSheaf hX M hM)

variable (hG : Langlands.Topology.IsLocallyProfinite G)

/-- The actual reconstruction functor on smooth compatible modules and all their maps. -/
def smoothFunctor :
    CompactSectionActions.SmoothCompatibleTestAction (G := G) (X := X) ⥤
      SectionActions.SmoothActionSheaf G X :=
  (SectionActions.smoothActionProperty G X).lift
    ((CompactSectionActions.smoothProperty (G := G) (X := X)).ι ⋙
      ProjectorActionSheaf.functor hX)
    (fun M => isSmoothAction hX M.obj hG M.property)

/-- Forgetting smoothness keeps the constructed action sheaf and the original maps. -/
def smoothFunctorToActionIso :
    smoothFunctor hX hG ⋙ SectionActions.smoothActionInclusion G X ≅
      (CompactSectionActions.smoothProperty (G := G) (X := X)).ι ⋙
        ProjectorActionSheaf.functor hX :=
  (SectionActions.smoothActionProperty G X).liftCompιIso _ _

end RenardSmooth

end Langlands.Sheaf.Renard.SmoothProjectorActionSheaf
