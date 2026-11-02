import Langlands.Sheaf.Renard.GermSupportClosednessStatement
import Langlands.Sheaf.Renard.BasisStalkRepresentatives

/-!
# Renard II.2.2: local vanishing and relative support closedness

Common-refinement equality makes a local original representative zero on a
smaller basis neighborhood. The relative zero locus is therefore open.
-/

open TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- A zero value of the original germ section vanishes on a contained basis neighborhood. -/
theorem rawGermLocalVanishing (F : RawPresheaf.{u,v} B) :
    RawGermLocalVanishingStatement F := by
  intro U s x hx
  obtain ⟨W, hxW, hWU, t, ht⟩ := s.property x
  have hzero : rawGerm F W x.val hxW t = rawGerm F W x.val hxW 0 := by
    rw [ht x.val hxW, rawGerm_zero]
    exact hx
  obtain ⟨V, hxV, hVW, _, heq⟩ :=
    (rawGerm_eq_iff F x.val W W hxW hxW t 0).mp hzero
  have hrest : restriction F hVW t = 0 := by
    simpa only [map_zero] using heq
  refine ⟨V, hxV, hVW.trans hWU, ?_⟩
  intro y hy
  calc
    s.val ⟨y, (hVW.trans hWU) hy⟩ = rawGerm F W y (hVW hy) t :=
      (ht y (hVW hy)).symm
    _ = rawGerm F V y hy (restriction F hVW t) :=
      (rawGerm_restriction F hVW y hy t).symm
    _ = 0 := by rw [hrest, rawGerm_zero]

/-- The complement of the literal support is open in the actual domain subtype. -/
theorem rawGermRelativeSupportClosedness (F : RawPresheaf.{u,v} B) :
    RawGermRelativeSupportClosednessStatement F := by
  intro U s
  apply isOpen_compl_iff.mp
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  have hx0 : s.val x = 0 := by
    simpa only [Set.mem_compl_iff, mem_germSupport, not_not] using hx
  obtain ⟨V, hxV, hVU, hvan⟩ := rawGermLocalVanishing F U s x hx0
  refine ⟨(Subtype.val : U → X) ⁻¹' (V.obj : Set X), ?_,
    V.obj.isOpen.preimage continuous_subtype_val, hxV⟩
  intro y hy
  exact fun hne => hne (hvan y.val hy)

/-- Local vanishing for the normalized presheaf's unchanged underlying raw object. -/
theorem normalizedGermLocalVanishing (F : Presheaf.{u,v} B) :
    NormalizedGermLocalVanishingStatement F :=
  rawGermLocalVanishing F.obj

/-- Relative support closedness for exactly the normalized raw object. -/
theorem normalizedGermRelativeSupportClosedness (F : Presheaf.{u,v} B) :
    NormalizedGermRelativeSupportClosednessStatement F :=
  rawGermRelativeSupportClosedness F.obj

/-- The complete local-vanishing and relative-support-closedness aggregate. -/
theorem germSupportClosedness : GermSupportClosednessStatement.{u,v} := by
  intro X _ B
  exact ⟨rawGermLocalVanishing, rawGermRelativeSupportClosedness,
    normalizedGermLocalVanishing, normalizedGermRelativeSupportClosedness⟩

end Langlands.Sheaf.Renard
