/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood

/-!
# A flat finite depth-two extension is formally unramified

## References

* Stacks Project, Tag 0BJH, as applied in Tag 0EY6(3)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Flatness removes ramification of a finite depth-two extension of an etale cover. -/
theorem formallyUnramified_of_flat_depth_two_finite_extension
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Flat p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    FormallyUnramified p := by
  classical
  let : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  have hdim (z : E) :
      (IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z) : WithBot ℕ∞) ≤
        ringKrullDim (E.presheaf.stalk z) := by
    simpa only [Module.supportDim_self_eq_ringKrullDim] using
      IsLocalRing.depth_le_supportDim (R := E.presheaf.stalk z) (E.presheaf.stalk z)
  have hopen : FormallyUnramified ((p ⁻¹ᵁ U).ι ≫ p) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hneighbourhood (z : E) :
      ∃ V : E.Opens, z ∈ V ∧ FormallyUnramified (V.ι ≫ p) := by
    by_cases hz : p z ∈ U
    · exact ⟨p ⁻¹ᵁ U, hz, hopen⟩
    · have htwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (E.presheaf.stalk z) :=
        (WithBot.coe_le_coe.mpr (hboundary z hz)).trans (hdim z)
      have hunram (z' : E) (_ : Specializes z' z)
          (hdimOne : ringKrullDim (E.presheaf.stalk z') = 1) :
          ∃ V : E.Opens, z' ∈ V ∧ FormallyUnramified (V.ι ≫ p) := by
        have hz'U : p z' ∈ U := by
          by_contra hz'
          have hbad : (2 : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
            simpa only [hdimOne, WithBot.coe_ofNat] using
              (WithBot.coe_le_coe.mpr (hboundary z' hz')).trans (hdim z')
          norm_num at hbad
        exact ⟨p ⁻¹ᵁ U, hz'U, hopen⟩
      obtain ⟨V, hzV, hV⟩ :=
        exists_etale_neighbourhood_of_finite_flat_of_codimension_one p z
          (lt_of_lt_of_le (by norm_num) htwo) hunram
      let := hV
      exact ⟨V, hzV, inferInstance⟩
  choose V hzV hV using hneighbourhood
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @FormallyUnramified) V
    (eq_top_iff.mpr (fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩))
  exact hV

end AlgebraicGeometry.Scheme
