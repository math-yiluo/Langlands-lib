/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
/-!
# Etale descent from a flat base change near a closed fibre

## References

* Stacks Project, Tag 0EYA, final omitted detail
* Tag 02VN
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Etaleness descends from a flat Noetherian base change when it holds over
an open containing a point above the closed point of the local base. -/
theorem etale_of_flat_base_change_near_closed_point
    (B : Type u) [CommRing B] [IsLocalRing B]
    {Y T E : Scheme.{u}} [IsNoetherian T] (g : Y ⟶ Spec (.of B))
    (t : T ⟶ Spec (.of B)) [Flat t] (a : E ⟶ Y) (p : E ⟶ T)
    (H : IsPullback a p g t) (V : T.Opens) [Etale (p ∣_ V)]
    (v : T) (hv : v ∈ V) (hclosed : t v = IsLocalRing.closedPoint B) :
    Etale g := by
  let tV := V.ι ≫ t
  have : Flat tV := inferInstance
  have : Surjective tV := by
    refine ⟨fun b ↦ ?_⟩
    obtain ⟨w, hw, hwb⟩ := Flat.generalizingMap tV (a := (⟨v, hv⟩ : V.toScheme)) (b := b) (by
        change Specializes b (t v)
        rw [hclosed]
        exact IsLocalRing.specializes_closedPoint b)
    exact ⟨w, hwb⟩
  have : QuasiCompact tV := inferInstance
  have H' := Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := ⊤)
    (by simp) (by simp) (UY := p ⁻¹ᵁ V) (by simp)
  have hp' : Etale (p.resLE V (p ⁻¹ᵁ V) le_rfl) := by
    simpa only [Hom.resLE_eq_morphismRestrict] using (inferInstance : Etale (p ∣_ V))
  have hg' : Etale (g.resLE ⊤ ⊤ (by simp)) := by
    apply MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H'.flip
    · have hqc : QuasiCompact (t.resLE ⊤ V (by simp)) := by
        apply (MorphismProperty.cancel_right_of_respectsIso @QuasiCompact
          (t.resLE ⊤ V (by simp)) (Spec (.of B)).topIso.hom).mp
        rw [Scheme.topIso_hom, Hom.resLE_comp_ι]
        infer_instance
      refine ⟨⟨?_, inferInstance⟩, hqc⟩
      refine ⟨fun b ↦ ?_⟩
      obtain ⟨w, hw⟩ := Surjective.surj (f := tV) b.1
      refine ⟨w, ?_⟩
      apply Subtype.ext
      simpa only [Hom.coe_resLE_apply, tV, Hom.comp_apply, Scheme.Opens.ι_apply] using hw
    · exact hp'
  have : Etale ((⊤ : Y.Opens).ι ≫ g) := by
    rw [← Hom.resLE_comp_ι g (show (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤ by simp)]
    infer_instance
  rw [← MorphismProperty.cancel_left_of_respectsIso @Etale Y.topIso.hom]
  simpa only [Scheme.topIso_hom] using this

end AlgebraicGeometry.Scheme
