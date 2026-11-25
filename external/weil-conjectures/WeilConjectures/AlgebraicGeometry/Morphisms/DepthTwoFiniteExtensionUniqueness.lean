/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomEquality
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec

/-!
# Uniqueness of finite extensions with depth two at the boundary

## References

* Stacks Project, Tag 0EY6, proof of assertion (2)
* Stacks Project, Tag 0EY6, converse in the proof of (2)
* Tags 0AUK and 0E9I
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An isomorphism on an open extends between finite schemes of depth at least
two above its complement. No etaleness or depth assumption on the base is needed. -/
theorem iso_of_finite_depth_two_extensions
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsFinite p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (hE : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (e : (p ⁻¹ᵁ U).toScheme ≅ (r ⁻¹ᵁ U).toScheme)
    (he : e.hom ≫ r ∣_ U = p ∣_ U) :
    ∃ i : F ≅ E, i.hom ≫ p = r := by
  have hei : e.inv ≫ p ∣_ U = r ∣_ U := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨f, hf, hfu⟩ := exists_hom_of_finite_depth_two U r p hF e.inv hei
  obtain ⟨g, hg, hgu⟩ := exists_hom_of_finite_depth_two U p r hE e.hom he
  have hfg : f ≫ g = 𝟙 F := by
    apply hom_eq_of_finite_depth_two U r r hF
      (f ≫ g) (𝟙 F) (by rw [Category.assoc, hg, hf]) (by simp)
    rw [← Category.assoc, hfu, Category.assoc, hgu, ← Category.assoc]
    simp
  have hgf : g ≫ f = 𝟙 E := by
    apply hom_eq_of_finite_depth_two U p p hE
      (g ≫ f) (𝟙 E) (by rw [Category.assoc, hf, hg]) (by simp)
    rw [← Category.assoc, hgu, Category.assoc, hfu, ← Category.assoc]
    simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end AlgebraicGeometry.Scheme
