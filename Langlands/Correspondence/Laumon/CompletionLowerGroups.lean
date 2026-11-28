import Langlands.Correspondence.Laumon.CompletionDensity

/-!
# Lower and upper ramification groups across the completion

For a finite field `k`, if restriction `completionRestriction k` is a homeomorphism, the
Library's lower ramification groups of every finite Galois level `L` of `LaurentSeries k` are
given by the congruences `HenselianLowerTest` on the henselian elements of `L`, and the image of
the absolute upper ramification group of every level is described by these congruences at the
index `⌈ψ_L(v)⌉`.
-/

noncomputable section

universe u

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

open IsLocalRing ValuativeRel
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed Langlands.Ramification.Local
open scoped NNReal

variable {k : Type u} [Field k] [Finite k]

local notation "X" => LaurentSeries k
local notation "Ωx" => SeparableClosure (LaurentSeries k)

omit [Finite k] in
/-- After coercion to the separable closure, finite restriction acts as the original
automorphism. -/
theorem absoluteFiniteRestriction_apply (L : FiniteGaloisIntermediateField X Ωx)
    (σ : Gal(Ωx/X)) (x : L) :
    ((absoluteFiniteRestriction X Ωx L σ x : L) : Ωx) = σ (x : Ωx) :=
  AlgEquiv.restrictNormalHom_apply L.toIntermediateField σ x

/-- The Library's valuation of the separable closure is invariant under automorphisms. -/
theorem closureValuation_map (σ : Gal(Ωx/X)) (x : Ωx) :
    closureValuation X Ωx (σ x) = closureValuation X Ωx x :=
  closureValuation_algEquiv_apply X Ωx σ x

variable (hr : IsHomeomorph (completionRestriction k))
include hr

/-- **Clause 5.** If restriction is a homeomorphism, the restriction of `σ` to a finite Galois
level `L` lies in the Library's `i`-th lower ramification group exactly when the restriction of
`σ` to the separable generic closure passes `HenselianLowerTest k L i`. -/
theorem mem_lowerRamificationGroup_iff_henselianLowerTest
    (L : FiniteGaloisIntermediateField X Ωx) (σ : Gal(Ωx/X)) (i : ℕ) :
    absoluteFiniteRestriction X Ωx L σ ∈
        lowerRamificationGroup (localTopologicalData X L) X i ↔
      HenselianLowerTest k L i (completionRestriction k σ) := by
  obtain ⟨π, hπ0, hπ1, hπ⟩ := exists_levelUniformizer X Ωx L
  rw [mem_lowerRamificationGroup_iff_closureValuation hπ1 hπ]
  have hcoe : ∀ x : L, (((absoluteFiniteRestriction X Ωx L σ x - x : L)) : Ωx) =
      σ (x : Ωx) - (x : Ωx) := fun x => by
    rw [AddSubgroupClass.coe_sub, absoluteFiniteRestriction_apply]
  obtain ⟨ϖ, hϖS, hϖπ⟩ := exists_henselianLevel_closureValuation_lt hr L π.2 hπ0
  have hϖv : closureValuation X Ωx ϖ = closureValuation X Ωx (π : Ωx) := by
    have h := Valuation.map_sub_eq_of_lt_left (closureValuation X Ωx) hϖπ
    rwa [sub_sub_cancel] at h
  constructor
  · intro h
    refine ⟨⟨ϖ, hϖS.1⟩, hϖS.2, by rw [hϖv]; exact hπ1, ?_, ?_⟩
    · intro x hxL hx1
      rw [hϖv]
      exact hπ ⟨x, hxL⟩ hx1
    · intro b hbL hb1
      rw [hϖv, completionRestriction_apply]
      have := h ⟨b, hbL⟩ hb1
      rwa [hcoe] at this
  · rintro ⟨ϖ', hϖ'L, hϖ'1, hϖ'max, hcong⟩
    have hv' : closureValuation X Ωx (ϖ' : Ωx) = closureValuation X Ωx (π : Ωx) := by
      refine le_antisymm (hπ ⟨ϖ', hϖ'L⟩ hϖ'1) ?_
      rw [← hϖv]
      exact hϖ'max ⟨ϖ, hϖS.1⟩ hϖS.2 (by rw [hϖv]; exact hπ1)
    intro x hx
    rw [hcoe]
    have hγ : 0 < closureValuation X Ωx (π : Ωx) ^ (i + 1) := pow_pos hπ0 _
    obtain ⟨b, hbS, hxb⟩ := exists_henselianLevel_closureValuation_lt hr L x.2 hγ
    have hle1 : closureValuation X Ωx (π : Ωx) ^ (i + 1) ≤ 1 := pow_le_one₀ zero_le hπ1.le
    have hb1 : closureValuation X Ωx b ≤ 1 := by
      have : b = (x : Ωx) - ((x : Ωx) - b) := by ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans (max_le hx (hxb.le.trans hle1))
    have hcb := hcong ⟨b, hbS.1⟩ hbS.2 hb1
    rw [completionRestriction_apply, hv'] at hcb
    have hsplit : σ (x : Ωx) - (x : Ωx) =
        (σ b - b) + (σ ((x : Ωx) - b) - ((x : Ωx) - b)) := by
      rw [map_sub]
      ring
    rw [hsplit]
    refine (Valuation.map_add _ _ _).trans (max_le hcb ?_)
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ hxb.le)
    rw [closureValuation_map]
    exact hxb.le

/-- **Clause 6.** If restriction is a homeomorphism, the image of the Library's absolute upper
ramification group of level `v` consists of the automorphisms passing, at every finite Galois
level `L`, the henselian lower test of index `⌈ψ_L(v)⌉` (or with `⌈ψ_L(v)⌉ < 0`). -/
theorem mem_map_localAbsoluteUpperRamificationGroup_iff (v : ℝ)
    (τ : Gal(endGenericClosure k/endField k)) :
    τ ∈ (localAbsoluteUpperRamificationGroup X Ωx v).map (completionRestriction k) ↔
      ∀ L : FiniteGaloisIntermediateField X Ωx,
        ⌈herbrandPsi (localTopologicalData X L) X v⌉ < 0 ∨
          HenselianLowerTest k L (⌈herbrandPsi (localTopologicalData X L) X v⌉).toNat τ := by
  have hmem : ∀ σ : Gal(Ωx/X), σ ∈ localAbsoluteUpperRamificationGroup X Ωx v ↔
      ∀ L : FiniteGaloisIntermediateField X Ωx,
        ⌈herbrandPsi (localTopologicalData X L) X v⌉ < 0 ∨
          HenselianLowerTest k L (⌈herbrandPsi (localTopologicalData X L) X v⌉).toNat
            (completionRestriction k σ) := by
    intro σ
    unfold localAbsoluteUpperRamificationGroup
    rw [mem_absoluteUpperRamificationGroup_iff_lower]
    refine forall_congr' fun L => ?_
    rw [← mem_lowerRamificationGroup_iff_henselianLowerTest hr L σ]
    exact mem_lowerRamificationGroupInt_iff (localTopologicalData X L) X _ _
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (hmem σ).mp hσ
  · intro h
    obtain ⟨σ, rfl⟩ := hr.bijective.surjective τ
    exact ⟨σ, (hmem σ).mpr h, rfl⟩

end Langlands.Henniart.Laumon
