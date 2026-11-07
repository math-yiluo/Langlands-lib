import Langlands.Geometry.Building.AffineChamberWallComparisonProof
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Group.TitsSystemRestricted
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # Admissibility of singleton types in an actual affine chamber -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Langlands.Group.TitsSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Distinct parallel roots with the same derivative have noncommuting reflections.
The coroots need not first be identified. -/
theorem affineReflection_mul_ne_of_linear_eq
    {ψ η : A →ᵃ[ℝ] ℝ} {v w : V}
    (hv : ψ.linear v = 2) (hw : η.linear w = 2)
    (hlin : η.linear = ψ.linear) (hne : η ≠ ψ) :
    affineReflection ψ hv * affineReflection η hw ≠
      affineReflection η hw * affineReflection ψ hv := by
  intro hcomm
  apply hne
  apply AffineMap.ext
  intro x
  have hψw : ψ.linear w = 2 := hlin ▸ hw
  have hηv : η.linear v = 2 := by rw [hlin]; exact hv
  have hψη : ∀ y, ψ (affineReflection η hw y) = ψ y - 2 * η y := by
    intro y
    rw [affineReflection_apply, AffineMap.map_vadd, map_smul, hψw,
      smul_eq_mul, vadd_eq_add]
    ring
  have hηψ : ∀ y, η (affineReflection ψ hv y) = η y - 2 * ψ y := by
    intro y
    rw [affineReflection_apply, AffineMap.map_vadd, map_smul, hηv,
      smul_eq_mul, vadd_eq_add]
    ring
  have H := congrArg (fun e : A ≃ᵃ[ℝ] A => ψ (e x)) hcomm
  change ψ (affineReflection ψ hv (affineReflection η hw x)) =
    ψ (affineReflection η hw (affineReflection ψ hv x)) at H
  rw [apply_affineReflection, hψη, hψη, apply_affineReflection, hηψ] at H
  linarith

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

include hΨ

/-- Corrected AR4 gives a root with the same derivative and a distinct affine constant. -/
theorem exists_distinct_parallel_root {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    ∃ η ∈ Ψ, η.linear = ψ.linear ∧ η ≠ ψ := by
  obtain ⟨η, ⟨hη, hlin⟩, hne⟩ :=
    (hΨ.infinite_fiber ψ hψ).exists_notMem_finite (Set.finite_singleton ψ)
  exact ⟨η, hη, hlin, fun heq => hne (Set.mem_singleton_iff.mpr heq)⟩

/-- Every actual root reflection has a noncommuting parallel reflection in the same
affine Weyl group. -/
theorem exists_noncommuting_parallel_reflection
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) {v : V} (hv : IsCoroot Ψ ψ v) :
    ∃ t : affineWeylGroup Ψ,
      (∃ η ∈ Ψ, η.linear = ψ.linear ∧ η ≠ ψ ∧
        ∃ (w : V) (hw : IsCoroot Ψ η w), t.val = affineReflection η hw.1) ∧
      affineReflection ψ hv.1 * t.val ≠ t.val * affineReflection ψ hv.1 := by
  obtain ⟨η, hη, hlin, hne⟩ := hΨ.exists_distinct_parallel_root hψ
  obtain ⟨w, hw⟩ := hΨ.exists_isCoroot η hη
  exact ⟨⟨affineReflection η hw.1, affineReflection_mem_affineWeylGroup hη hw⟩,
    ⟨η, hη, hlin, hne, w, hw, rfl⟩,
    affineReflection_mul_ne_of_linear_eq hv.1 hw.1 hlin hne⟩

/-- A chosen actual parallel reflection which does not commute with the given root
reflection. Its subtype retains the root, parallelism, distinctness, coroot and
equality with the root reflection; both act on the original affine space. -/
def noncommutingParallelReflection
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) {v : V} (hv : IsCoroot Ψ ψ v) :
    {t : affineWeylGroup Ψ //
      (∃ η ∈ Ψ, η.linear = ψ.linear ∧ η ≠ ψ ∧
        ∃ (w : V) (hw : IsCoroot Ψ η w), t.val = affineReflection η hw.1) ∧
      affineReflection ψ hv.1 * t.val ≠ t.val * affineReflection ψ hv.1} :=
  ⟨(hΨ.exists_noncommuting_parallel_reflection hψ hv).choose,
    (hΨ.exists_noncommuting_parallel_reflection hψ hv).choose_spec⟩

/-- The proved wall comparison and wall generation apply to every affine chamber. -/
theorem closure_chamberSimpleReflections {C : Set A} (hC : IsChamber Ψ C) :
    Subgroup.closure (chamberSimpleReflections Ψ C) = ⊤ := by
  obtain ⟨x, hx, rfl⟩ := hC
  exact closure_chamberSimpleReflections_eq_top_of_wall_generation _ x
    (Langlands.Geometry.Building.affineChamberWallComparison V A Ψ hΨ x hx)
    (Langlands.Geometry.Building.affineReflectionGalleryGeometry V A Ψ
      hΨ.isLocallyFiniteReflectionArrangement x hx).1

/-- No chamber-simple reflection is isolated from all other simple reflections in
the noncommutation graph. -/
theorem exists_noncommuting_chamberSimpleReflection
    {C : Set A} (hC : IsChamber Ψ C) {s : affineWeylGroup Ψ}
    (hs : s ∈ chamberSimpleReflections Ψ C) :
    ∃ t ∈ chamberSimpleReflections Ψ C, s * t ≠ t * s := by
  by_contra! h
  have hle : Subgroup.closure (chamberSimpleReflections Ψ C) ≤
      Subgroup.centralizer ({s} : Set (affineWeylGroup Ψ)) := by
    apply (Subgroup.closure_le _).mpr
    intro t ht
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      simpa only [hx] using h t ht)
  rw [hΨ.closure_chamberSimpleReflections hC] at hle
  obtain ⟨ψ, hψ, v, hv, hsψ⟩ := hs
  let t := hΨ.noncommutingParallelReflection hψ.1.1 hv
  have hcomm : s * t.val = t.val * s :=
    (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top t.val))) s
      (Set.mem_singleton s)
  have H := congrArg (fun w : affineWeylGroup Ψ => (w : A ≃ᵃ[ℝ] A)) hcomm
  change (s : A ≃ᵃ[ℝ] A) * t.val.val = t.val.val * (s : A ≃ᵃ[ℝ] A) at H
  rw [hsψ] at H
  exact t.property.2 H

/-- In an affine chamber, every singleton simple-reflection type is admissible
for the existing restricted-building convention. -/
theorem isAdmissibleType_singleton_chamberSimpleReflections
    {C : Set A} (hC : IsChamber Ψ C) {s : affineWeylGroup Ψ}
    (hs : s ∈ chamberSimpleReflections Ψ C) :
    IsAdmissibleType (chamberSimpleReflections Ψ C) {s} := by
  refine ⟨Set.singleton_subset_iff.mpr hs, ?_⟩
  intro r hr
  by_cases hrs : r = s
  · subst r
    obtain ⟨t, ht, hst⟩ := hΨ.exists_noncommuting_chamberSimpleReflection hC hs
    refine ⟨t, ht, Relation.ReflTransGen.single ⟨hs, ht, hst⟩, ?_⟩
    intro hts
    rw [Set.mem_singleton_iff] at hts
    exact hst (by rw [hts])
  · exact ⟨r, hr, Relation.ReflTransGen.refl, fun h => hrs (Set.mem_singleton_iff.mp h)⟩

end IsAffineRootSystemWithRankZero
end Langlands.Geometry.Building.AffineRootSystem
