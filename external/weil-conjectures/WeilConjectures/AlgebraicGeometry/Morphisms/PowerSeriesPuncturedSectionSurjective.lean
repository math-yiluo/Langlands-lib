/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedHomAlgebraization

/-!
# Surjectivity of restriction on the punctured power-series section

## References

* Stacks Project, Tags 0EY9, 0BK0, 0EKP and 0EL8
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Surjectivity of restriction on morphisms of finite étale covers in the
power-series punctured-section situation (the lifting part of Stacks Project, Tag 0EY9). -/
theorem finiteEtale_powerSeries_punctured_section_restriction_surjective
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))
    ∀ P Q : V.toScheme.FiniteEtale,
      Function.Surjective ((FiniteEtale.pullback (z ∣_ V)).map (X := P) (Y := Q)) := by
  classical
  dsimp only
  intro P Q φ
  let f := MvPowerSeries.constantCoeff (σ := Fin d) (R := A)
  have hf : Function.Surjective f := by
    intro a
    exact ⟨MvPowerSeries.C (σ := Fin d) a, by simp [f]⟩
  have hlift (n : ℕ) := finiteEtale_adic_unique_lift f hf V P Q φ n
  choose g hg huniq using hlift
  have hcompat (n : ℕ) :
      FiniteEtale.Adic.coverTransition f V P n ≫ g (n + 1) = g n := by
    apply huniq n
    constructor
    · rw [Category.assoc, (hg (n + 1)).1, ← Category.assoc,
        FiniteEtale.Adic.coverTransition_coverMap]
    · rw [← Category.assoc, FiniteEtale.Adic.zeroMap_coverTransition, (hg (n + 1)).2]
  obtain ⟨ψ, hψ, hformal⟩ :=
    finiteEtale_powerSeries_punctured_formal_hom_algebraization
      A hdepth d hd V hV P Q g (fun n ↦ (hg n).1) hcompat
  let Ψ : P ⟶ Q := ObjectProperty.homMk (MorphismProperty.Over.homMk ψ hψ)
  refine ⟨Ψ, ?_⟩
  apply FiniteEtale.hom_ext
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [FiniteEtale.pullback_map_hom_left,
      CategoryTheory.Limits.pullback.lift_fst]
    change CategoryTheory.Limits.pullback.fst _ _ ≫ ψ = _
    rw [← FiniteEtale.Adic.zeroMap_coverMap f V P 0, Category.assoc, hformal 0]
    exact (hg 0).2
  · simpa only [FiniteEtale.pullback_map_hom_left,
      CategoryTheory.Limits.pullback.lift_snd, Category.comp_id,
      FiniteEtale.pullback_obj_obj_hom] using
        (FiniteEtale.hom_left_comp φ).symm

end AlgebraicGeometry.Scheme
