/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Lifting generalizations in the closed fibre of a flat chart

## References

* Stacks Project, Tags 0EYB and 00HS, closed-fibre base change and going down
* Stacks Project, Tag 0EYB, the closed-fibre image argument
* Tag 00HS, going down
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- A flat morphism to a base-changed scheme lifts generalizations in the original
closed fibre to generalizations over the closed point of the changed base. -/
theorem exists_closed_fiber_generalization_lifts
    (A B R : Type u) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing R]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A))
    (φ : A →+* B) [IsLocalHom φ] (c : B →+* R)
    (t : Spec (.of R) ⟶ Limits.pullback q (Spec.map (CommRingCat.ofHom φ))) [Flat t]
    (ht : t ≫ Limits.pullback.snd q (Spec.map (CommRingCat.ofHom φ)) =
      Spec.map (CommRingCat.ofHom c))
    (v : Spec (.of R)) (hv : PrimeSpectrum.comap c v = IsLocalRing.closedPoint B) :
    ∃ η : q.fiber (IsLocalRing.closedPoint A),
      (t ≫ Limits.pullback.fst q (Spec.map (CommRingCat.ofHom φ))) v =
        q.fiberι (IsLocalRing.closedPoint A) η ∧
      ∀ η', η' ⤳ η → ∃ w : Spec (.of R), w ⤳ v ∧
        PrimeSpectrum.comap c w = IsLocalRing.closedPoint B ∧
        (t ≫ Limits.pullback.fst q (Spec.map (CommRingCat.ofHom φ))) w =
          q.fiberι (IsLocalRing.closedPoint A) η' := by
  classical
  let g := Spec.map (CommRingCat.ofHom φ)
  let b : Spec (.of B) := IsLocalRing.closedPoint B
  let r := pullback.snd q g
  let f := t ≫ r
  have hg : g b = IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint φ
  rw [← hg]
  let d : f.fiber b ⟶ r.fiber b := pullback.lift
    (f.fiberι b ≫ t) (f.fiberToSpecResidueField b) (by
      simpa only [f, Category.assoc] using f.fiber_fac b)
  have hd₁ : d ≫ r.fiberι b = f.fiberι b ≫ t := by simp [d, Hom.fiberι]
  have hd₂ : d ≫ r.fiberToSpecResidueField b = f.fiberToSpecResidueField b := by
    simp [d, Hom.fiberToSpecResidueField]
  have hd : IsPullback d (f.fiberι b) (r.fiberι b) t := by
    apply IsPullback.of_right (h₁₂ := r.fiberToSpecResidueField b)
      (h₂₂ := r) (v₁₃ := (Spec (.of B)).fromSpecResidueField b)
    · rw [hd₂]
      exact (IsPullback.of_hasPullback f _).flip
    · exact hd₁
    · exact (IsPullback.of_hasPullback r _).flip
  have : Flat d := MorphismProperty.of_isPullback hd.flip inferInstance
  let e : r.fiber b ⟶ q.fiber (g b) := pullback.map _ _ _ _
    (pullback.fst q g) (Spec.map (g.residueFieldMap b)) g
    (pullback.condition.symm) (by simp)
  have he := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback q g) b
  have hfield : Flat (Spec.map (g.residueFieldMap b)) := by
    rw [Flat.SpecMap_iff]
    dsimp only [RingHom.Flat]
    infer_instance
  have : Flat e := MorphismProperty.of_isPullback he.flip hfield
  let F := d ≫ e
  have hF : F ≫ q.fiberι (g b) = f.fiberι b ≫ t ≫ pullback.fst q g := by
    simp [F, e, Hom.fiberι, Category.assoc, d, pullback.map]
  have hFpoint (z : f.fiber b) :
      q.fiberι (g b) (F z) = (t ≫ pullback.fst q g) (f.fiberι b z) := by
    simpa only [Hom.comp_apply] using (congrArg (fun k ↦ k z) hF)
  have hvf : f v = b := by
    change (t ≫ r) v = b
    rw [ht]
    exact hv
  let v₀ := (f.fiberHomeo b).symm ⟨v, hvf⟩
  have hv₀ : f.fiberι b v₀ = v := f.fiberι_fiberHomeo_symm b ⟨v, hvf⟩
  refine ⟨F v₀, ?_, ?_⟩
  · exact (congrArg (t ≫ pullback.fst q g) hv₀).symm.trans (hFpoint v₀).symm
  · intro η' hgen
    obtain ⟨w₀, hw₀, hwi⟩ := Flat.generalizingMap F hgen
    refine ⟨f.fiberι b w₀, ?_, ?_, ?_⟩
    · simpa only [hv₀] using hw₀.map (f.fiberι b).continuous
    · change (Spec.map (CommRingCat.ofHom c)) (f.fiberι b w₀) = b
      rw [← ht]
      exact (f.fiberHomeo b w₀).2
    · rw [← hwi]
      exact (hFpoint w₀).symm

end AlgebraicGeometry.Scheme
