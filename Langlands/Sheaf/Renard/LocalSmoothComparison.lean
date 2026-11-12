import Langlands.Sheaf.Renard.SectionActions
import Langlands.Sheaf.CompactGerms
import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Local and compact-section smoothness

Compact zero extension identifies Renard's smooth action condition with the
existing local smoothness condition on a locally profinite base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions

open CategoryTheory Opposite TopologicalSpace
open Langlands.Sheaf.Equivariant

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

omit [ContinuousSMul G X] in
/-- A fixed global section is locally fixed on every stable smaller open. -/
theorem isLocallyFixedAt_of_globalFixed [HasStableNeighbourhoods G X]
    (F : ActionSheaf G X) (s : F.obj.obj (op ActionOpens.top))
    (K : OpenSubgroup G)
    (hs : ∀ k : (K : Subgroup G), globalRepresentation F k s = s)
    (U : ActionOpens G X) (x : X) (hx : x ∈ U.openSet) :
    IsLocallyFixedAt ℂ F.obj
      ((F.obj.map (ActionOpens.inclusionHom (U := U) le_top).op).hom s) x := by
  obtain ⟨H, V, hVo, hxV, hVU, hV⟩ :=
    HasStableNeighbourhoods.exists_stable (G := G) x U.openSet U.openSet.isOpen hx
  let W : ActionOpens G X := ⟨⟨V, hVo⟩⟩
  have hWU : W.openSet ≤ U.openSet := hVU
  let L := H ⊓ K
  let hW : ∀ h : (L : Subgroup G), ∀ y ∈ W.openSet, (h : G) • y ∈ W.openSet :=
    fun h y hy => hV h (OpenSubgroup.mem_inf.1 h.2).1 y hy
  refine ⟨W, hWU, L, hW, hxV, ?_⟩
  intro h
  rw [map_inclusionHom_map_inclusionHom ℂ F.obj hWU le_top s]
  have e : ActionOpens.invariantArrow (L : Subgroup G) W hW h ≫
      ActionOpens.inclusionHom (U := W) le_top =
    ActionOpens.inclusionHom (U := W) le_top ≫ ActionOpens.sectionArrow (h : G) :=
    ActionOpens.Hom.ext (by simp [ActionOpens.invariantArrow,
      ActionOpens.inclusionHom, ActionOpens.sectionArrow])
  have key := congrArg (fun f => (F.obj.map f.op).hom s) e
  simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at key
  refine key.trans ?_
  change (F.obj.map (ActionOpens.inclusionHom (U := W) le_top).op).hom
      (globalRepresentation F h s) = _
  rw [hs ⟨h, (OpenSubgroup.mem_inf.1 h.2).2⟩]

/-- On a locally profinite base, compact-section smoothness gives the
published local smoothness condition on every original local section. -/
theorem isSmoothSheaf_of_isSmoothAction [HasStableNeighbourhoods G X]
    (F : ActionSheaf G X) (hX : Langlands.Topology.IsLocallyProfinite X)
    (hF : IsSmoothAction F) : IsSmoothSheaf ℂ G X F := by
  let : T2Space X := hX.t2Space
  intro U s x hx
  obtain ⟨V, hxV, hVo, hVc, hVU⟩ :=
    hX.hasCompactOpenNeighborhoodBasis x U.openSet (U.openSet.isOpen.mem_nhds hx)
  let W : ActionOpens G X := ⟨⟨V, hVo⟩⟩
  let t := (F.obj.map (ActionOpens.inclusionHom (U := W) hVU).op).hom s
  let c := Langlands.Sheaf.CompactGerms.compactExtension
    (underlying F) W.openSet hVc.isClosed hVc t
  obtain ⟨K, hK⟩ := hF c
  have hfix : ∀ k : (K : Subgroup G), globalRepresentation F k c.val = c.val := by
    intro k
    exact congrArg Subtype.val ((Representation.mem_invariants _ _).1 hK k)
  have ht := isLocallyFixedAt_of_globalFixed F c.val K hfix W x hxV
  have he : (F.obj.map (ActionOpens.inclusionHom (U := W) le_top).op).hom c.val = t :=
    Langlands.Sheaf.CompactGerms.restrict_extend
      (underlying F) W.openSet hVc.isClosed t
  rw [he] at ht
  exact IsLocallyFixedAt.of_restrict ℂ hVU ht

/-- The local and all-compact-section smoothness conditions coincide. -/
theorem isSmoothAction_iff_isSmoothSheaf [HasStableNeighbourhoods G X]
    (F : ActionSheaf G X) (hX : Langlands.Topology.IsLocallyProfinite X) :
    IsSmoothAction F ↔ IsSmoothSheaf ℂ G X F :=
  ⟨isSmoothSheaf_of_isSmoothAction F hX,
    CompactSections.isSmooth_representation_of_isSmoothSheaf⟩

/-- Hausdorff t.d. topological groups supply the required stable neighbourhoods. -/
theorem hasStableNeighbourhoods_of_locallyProfinite [IsTopologicalGroup G]
    (hG : Langlands.Topology.IsLocallyProfinite G) :
    HasStableNeighbourhoods G X := by
  let : NonarchimedeanGroup G :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨K, _, hKU⟩ :=
          ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).1 hG).2 U hU
        exact ⟨K, hKU⟩ }
  infer_instance

/-- Renard's smooth-action category and the existing locally smooth category
have literally the same objects and maps, up to their property proofs. -/
def localSmoothEquivalence [HasStableNeighbourhoods G X]
    (hX : Langlands.Topology.IsLocallyProfinite X) :
    SmoothActionSheaf G X ≌ SmoothTopologicalSheaf ℂ G X where
  functor := ObjectProperty.ιOfLE
    (fun F => isSmoothSheaf_of_isSmoothAction F hX)
  inverse := ObjectProperty.ιOfLE
    (fun _ => CompactSections.isSmooth_representation_of_isSmoothSheaf)
  unitIso := NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Iso.refl _))

end Langlands.Sheaf.Renard.SectionActions
