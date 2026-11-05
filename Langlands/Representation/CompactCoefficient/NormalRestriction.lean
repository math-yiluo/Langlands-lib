import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.CompactCoefficient.AmbientProjector

/-! # Compact coefficients on normal subgroup restrictions -/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]
  (A : SmoothRep.{0, uG, uV} ℂ G)

/-- Compact-coefficient vectors for restriction to a normal subgroup are
preserved by every element of the ambient group. -/
theorem compactCoefficientVectors_restrict_ambient_stable
    (g : G) (v : A)
    (hv : v ∈ compactCoefficientVectors (SmoothRep.restrictSubgroup N A).representation) :
    A.representation g v ∈
      compactCoefficientVectors (SmoothRep.restrictSubgroup N A).representation := by
  let e := SmoothRep.normalSubgroupInverseConjugation N g
  let f : Representation.IntertwiningMap
      ((SmoothRep.restrictSubgroup N A).representation.comp e.toMonoidHom)
      (SmoothRep.restrictSubgroup N A).representation :=
    SmoothRep.restrictionConjugationMap N A g
  intro ℓ hℓ
  have hm : IsSmoothVector
      (Representation.dual
        ((SmoothRep.restrictSubgroup N A).representation.comp e.toMonoidHom))
      (dualIntertwining f ℓ) :=
    isSmoothVector_map (dualIntertwining f) hℓ
  have hm' := (isSmoothVector_dual_comp_continuousMulEquiv_iff
    (SmoothRep.restrictSubgroup N A).representation e (dualIntertwining f ℓ)).mp hm
  have hc := (hv (dualIntertwining f ℓ) hm').comp_homeomorph e.toHomeomorph
  change HasCompactSupport
    (matrixCoefficient (SmoothRep.restrictSubgroup N A).representation ℓ (f v))
  exact (matrixCoefficient_intertwining f ℓ
    (show (SmoothRep.restrictSubgroup N A) from v)).symm ▸ hc

/-- The vectors with compact smooth-dual coefficients on a normal subgroup,
as an actual ambient subrepresentation. -/
def compactRestrictionSubrepresentation : Subrepresentation A.representation where
  toSubmodule := compactCoefficientVectors (SmoothRep.restrictSubgroup N A).representation
  apply_mem_toSubmodule := compactCoefficientVectors_restrict_ambient_stable N A

@[simp]
theorem compactRestrictionSubrepresentation_toSubmodule :
    (compactRestrictionSubrepresentation N A).toSubmodule =
      compactCoefficientVectors (SmoothRep.restrictSubgroup N A).representation := rfl

/-- In an ambient irreducible, a single nonzero vector with compact coefficients
on a normal subgroup makes all restricted coefficients compact. -/
theorem hasCompactSmoothDualCoefficients_restrict_of_exists_compact_vector
    (hA : A.IsIrreducible)
    (h : ∃ v : A, v ≠ 0 ∧
      v ∈ compactCoefficientVectors (SmoothRep.restrictSubgroup N A).representation) :
    HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N A).representation := by
  let := hA
  let S := compactRestrictionSubrepresentation N A
  obtain ⟨v, hv, hvS⟩ := h
  have htop : S = ⊤ := by
    refine (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left ?_
    intro hbot
    have hv' : v ∈ S := hvS
    rw [hbot] at hv'
    exact hv hv'
  intro w ℓ hℓ
  have hw : w ∈ S := by rw [htop]; trivial
  exact hw ℓ hℓ

/-- A nonzero map from a compact-coefficient representation into a normal
subgroup restriction forces compact coefficients on the entire restriction
when the ambient representation is irreducible. -/
theorem hasCompactSmoothDualCoefficients_restrict_of_nonzero_map
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (hA : A.IsIrreducible) (σ : Representation ℂ N W)
    (hσ : HasCompactSmoothDualCoefficients σ)
    (f : σ.IntertwiningMap (SmoothRep.restrictSubgroup N A).representation)
    (hf : f ≠ 0) :
    HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N A).representation := by
  classical
  apply hasCompactSmoothDualCoefficients_restrict_of_exists_compact_vector N A hA
  have hnonzero : ∃ w : W, f w ≠ 0 := by
    by_contra h
    apply hf
    ext w
    exact not_not.mp (not_exists.mp h w)
  obtain ⟨w, hw⟩ := hnonzero
  exact ⟨f w, hw, range_le_compactCoefficientVectors f hσ ⟨w, rfl⟩⟩

end Langlands
