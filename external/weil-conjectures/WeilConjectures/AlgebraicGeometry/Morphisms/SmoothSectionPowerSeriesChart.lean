/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothSectionCompletionChart
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatPowerSeriesChartGenericImage

/-!
# Completion of a smooth section and its closed-fibre generic point

## References

* Stacks Project, Tag 0EYB, completion and the image of the extended maximal ideal
* Tags 05D5 and 00MB
* Stacks Project, Tag 0EYB, the completion paragraph
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Completing a smooth chart along a section produces a flat power-series chart. Its
extended maximal ideal maps to a point generic on a nonempty open of the original fibre.
The number of variables is allowed to be zero. -/
theorem exists_smooth_section_power_series_chart
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] (hflat : φ.Flat)
    (s : Spec (.of B) ⟶ L) (hs : s ≫ q = Spec.map (CommRingCat.ofHom φ)) :
    ∃ (n : ℕ) (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶ L), Flat t ∧
      t ≫ q = Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n))) ≫
        Spec.map (CommRingCat.ofHom φ) ∧
      t ((Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n))))
        (IsLocalRing.closedPoint B)) = s (IsLocalRing.closedPoint B) ∧
      ∃ (v : Spec (.of (MvPowerSeries (Fin n) B)))
        (η : q.fiber (IsLocalRing.closedPoint A))
        (W : (q.fiber (IsLocalRing.closedPoint A)).Opens),
        v.asIdeal = (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)) ∧
        t v = q.fiberι (IsLocalRing.closedPoint A) η ∧
        (W : Set (q.fiber (IsLocalRing.closedPoint A))).Nonempty ∧ ∀ z ∈ W, η ⤳ z := by
  let f := Spec.map (CommRingCat.ofHom φ)
  have : Flat f := Flat.SpecMap_iff.mpr hflat
  let p : Limits.pullback q f ⟶ Spec (.of B) := Limits.pullback.snd q f
  let s' : Spec (.of B) ⟶ Limits.pullback q f :=
    Limits.pullback.lift s (𝟙 _) (by simpa [f] using hs)
  have hs' : s' ≫ p = 𝟙 _ := Limits.pullback.lift_snd _ _ _
  obtain ⟨n, t', ht', hp, hsec⟩ :=
    exists_smooth_section_completion_chart B p s' hs'
  have : Flat t' := ht'
  let t := t' ≫ Limits.pullback.fst q f
  have ht : t ≫ q = Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n))) ≫
      Spec.map (CommRingCat.ofHom φ) := by
    change (t' ≫ Limits.pullback.fst q f) ≫ q = _
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    exact congrArg (fun a ↦ a ≫ f) hp
  have : Flat t := inferInstance
  obtain ⟨v, V, hV, x, hv, hx, hgeneric⟩ :=
    exists_flat_power_series_chart_generic_image A q B φ n t' hp
  have : LocallyOfFiniteType (q.fiberToSpecResidueField (IsLocalRing.closedPoint A)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd q _))
  have : IsLocallyNoetherian (q.fiber (IsLocalRing.closedPoint A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (q.fiberToSpecResidueField _)
  have : IsNoetherianRing Γ(q.fiber (IsLocalRing.closedPoint A), V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  obtain ⟨W, hWopen, hWne, hWsub⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({x} : Set V)) hgeneric
  let W' : (q.fiber (IsLocalRing.closedPoint A)).Opens :=
    ⟨V.ι '' W, V.ι.isOpenEmbedding.isOpenMap _ hWopen⟩
  refine ⟨n, t, inferInstance, ht, ?_, v, V.ι x, W', hv, hx,
    hWne.image V.ι, ?_⟩
  · have horigin :
        Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n))) ≫ t = s := by
      change (_ ≫ t') ≫ Limits.pullback.fst q f = s
      rw [hsec]
      exact Limits.pullback.lift_fst _ _ _
    exact congrArg (fun a ↦ a (IsLocalRing.closedPoint B)) horigin
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ((specializes_iff_mem_closure).mpr (hWsub hy)).map V.ι.continuous

end AlgebraicGeometry.Scheme
