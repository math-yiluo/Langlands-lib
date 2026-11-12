import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Langlands.Sheaf.Equivariant.SmoothCompactSupport

/-! # Compact sections and the smooth coreflector -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- A uniformly smooth global section belongs to the smooth subsheaf. -/
theorem global_mem_smoothSubmodule
    (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (s : F.obj (op ActionOpens.top))
    (hs : Langlands.IsSmoothVector (CompactSections.globalRepresentation F) s) :
    s ∈ smoothSubmodule R F ActionOpens.top := by
  obtain ⟨H, hH⟩ := hs
  intro x _
  let htop : ∀ h : (H : Subgroup G), ∀ y ∈ (ActionOpens.top : ActionOpens G X).openSet,
      (h : G) • y ∈ (ActionOpens.top : ActionOpens G X).openSet := fun _ _ _ => trivial
  refine ⟨ActionOpens.top, le_rfl, H, htop, trivial, fun h => ?_⟩
  have hi : ActionOpens.inclusionHom
      (show (ActionOpens.top : ActionOpens G X).openSet ≤ ActionOpens.top.openSet from le_rfl) =
      𝟙 (ActionOpens.top : ActionOpens G X) := ActionOpens.Hom.ext rfl
  have hh : ActionOpens.invariantArrow (H : Subgroup G) ActionOpens.top htop h =
      ActionOpens.sectionArrow (h : G) := ActionOpens.Hom.ext rfl
  rw [hi, op_id, F.map_id]
  exact hH h

/-- The smooth subsheaf inclusion preserves the support of each global section. -/
theorem support_smoothSubsheaf (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (s : ((smoothSubsheafFunctor R).obj F).obj.obj (op ActionOpens.top)) :
    Langlands.Sheaf.CompactSupport.support (CompactSections.ordinary F.obj) s.val =
      Langlands.Sheaf.CompactSupport.support
        (CompactSections.ordinary ((smoothSubsheafFunctor R).obj F).obj) s := by
  exact Langlands.Sheaf.CompactSupport.support_map_of_mono (X := TopCat.of X) (R := R)
    ((toSheaf G X (ModuleCat.{u} R)).map ((smoothSubsheafι R).app F)) s

/-- Include compact sections of the smooth subsheaf into smooth compact sections. -/
def smoothCompactComparison :
    smoothCoreflector R ⋙ smoothSheafCompactSections R G X ⟶
      SmoothCompactSections.smoothFunctor R G X where
  app F := SmoothRep.ofHom (Langlands.smoothLift
    (CompactSections.isSmooth_representation_of_isSmoothSheaf
      (isSmoothSheaf_smoothSubsheaf R F))
    (CompactSections.map ((smoothSubsheafι R).app F)))
  naturality F F' f := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext s
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The comparison is bijective on the actual sections. -/
theorem smoothCompactComparison_bijective (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    Function.Bijective (SmoothRep.hom ((smoothCompactComparison R G X).app F)) := by
  constructor
  · intro s t h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v => v.val.val) h
  · intro s
    have hlocal := global_mem_smoothSubmodule R G X F.obj s.val.val
      ((SmoothCompactSections.exists_preimage_iff F.obj s.val.val).1 ⟨s, rfl⟩).2
    let t : ((smoothSubsheafFunctor R).obj F).obj.obj (op ActionOpens.top) :=
      ⟨s.val.val, hlocal⟩
    have hc : IsCompact (Langlands.Sheaf.CompactSupport.support
        (CompactSections.ordinary ((smoothSubsheafFunctor R).obj F).obj) t) := by
      rw [← support_smoothSubsheaf R G X F t]
      exact s.val.property
    exact ⟨⟨t, hc⟩, Subtype.ext (Subtype.ext rfl)⟩

instance smoothCompactComparison_isIso (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    IsIso ((smoothCompactComparison R G X).app F) := by
  have : Mono ((smoothCompactComparison R G X).app F) :=
    (SmoothRep.mono_iff_injective _).2 (smoothCompactComparison_bijective R G X F).1
  have : Epi ((smoothCompactComparison R G X).app F) :=
    (SmoothRep.epi_iff_surjective _).2 (smoothCompactComparison_bijective R G X F).2
  exact isIso_of_mono_of_epi _

/-- Compact sections of the smooth coreflector are the smooth compact sections. -/
def smoothCompactComparisonIso :
    smoothCoreflector R ⋙ smoothSheafCompactSections R G X ≅
      SmoothCompactSections.smoothFunctor R G X :=
  NatIso.ofComponents (fun F => asIso ((smoothCompactComparison R G X).app F))
    (fun f => (smoothCompactComparison R G X).naturality f)

end Langlands.Cohomology.EquivariantComposite
