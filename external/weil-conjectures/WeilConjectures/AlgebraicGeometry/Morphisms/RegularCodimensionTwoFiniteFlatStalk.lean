/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteEtaleModel

/-!
# Flatness at a regular codimension-two boundary point

## References

* Stacks Project, Tags 0BMA, 0EY7 and 0EY6(2)
* Stacks Project, Tag 0BMA (local purity), Tag 0EY7 (Noetherian extension), and Tag 0EY6(2)
  (uniqueness of the depth-two extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A supplied finite depth-two extension has a flat stalk map at a missing point
when all missing target points are regular of local dimension at least two. -/
theorem flat_stalk_of_regular_codimension_two_depth_two_extension
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (hboundary : ∀ y : L, y ∉ V → IsRegularLocalRing (L.presheaf.stalk y) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk y))
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)]
    (hsource : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (z : E) :
    (p.stalkMap z).hom.Flat := by
  obtain ⟨F, r, hfin, het, hdepth, e, he⟩ :=
    exists_finite_etale_depth_two_model V hboundary p
  have : IsFinite r := hfin
  have : Etale r := het
  obtain ⟨i, hi⟩ := iso_of_finite_depth_two_extensions V r p hdepth hsource e he
  have hp : p = i.inv ≫ r := by
    rw [← hi, ← Category.assoc, i.inv_hom_id, Category.id_comp]
  have : Flat p := by
    rw [hp]
    infer_instance
  exact Flat.stalkMap p z

end AlgebraicGeometry.Scheme
