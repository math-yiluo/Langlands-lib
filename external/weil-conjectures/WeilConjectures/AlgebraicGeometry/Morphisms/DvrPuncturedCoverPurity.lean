/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatDvrSpecialFiberCartier
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity

/-!
# Purity for punctured covers of a smooth family over a DVR

## References

* Stacks Project, Tag 0EYE, as applied in the trait paragraph of Tag 0EYJ
* Stacks Project, Tag 0EYE, and Tag 0EYJ, first two paragraphs of the proof
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The purity step over a genuine DVR: a finite punctured cover with an etale
model meeting the special fibre admits a finite etale extension. This does not
assert normality of the extension or density of its puncture. -/
theorem exists_finite_etale_extension_of_dvr_neighbourhood
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {L N : Scheme.{u}} (q : L ⟶ Spec (.of A))
    [Smooth q] [GeometricallyConnected q]
    (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    (n : N ⟶ L) [IsFinite n]
    (het : Etale (n ∣_ (q ⁻¹ᵁ V)))
    (W : L.Opens) (x : L) (hx : x ∈ W)
    (hqx : q x = IsLocalRing.closedPoint A) (hW : Etale (n ∣_ W)) :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : (n ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ≅ (p ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme,
        e.hom ≫ (p ∣_ (q ⁻¹ᵁ V)) = n ∣_ (q ⁻¹ᵁ V) := by
  let s := IsLocalRing.closedPoint A
  let D := q.fiber s
  let i := q.fiberι s
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  have : Smooth (q.fiberToSpecResidueField s) := by
    dsimp [Hom.fiberToSpecResidueField]
    infer_instance
  have : IsLocallyNoetherian D :=
    LocallyOfFiniteType.isLocallyNoetherian (q.fiberToSpecResidueField s)
  have : IsRegular D := IsRegular.of_smooth (q.fiberToSpecResidueField s)
  have : ConnectedSpace D := inferInstanceAs (ConnectedSpace (q.fiber s))
  have : IsIntegral D := IsRegular.isIntegral D
  have hU : ∀ z : L, z ∈ q ⁻¹ᵁ V ↔ z ∉ Set.range i := by
    intro z
    rw [q.range_fiberι s]
    exact hV (q z)
  have hxrange : x ∈ Set.range i := by
    rw [q.range_fiberι s]
    exact hqx
  obtain ⟨y, hy⟩ := hxrange
  have hgeneric : i (genericPoint D) ∈ W := by
    exact ((genericPoint_specializes y).map i.continuous).mem_open W.isOpen (hy ▸ hx)
  exact exists_finite_etale_extension_of_regular_integral_divisor i
    (isEffectiveCartierCenter_specialFiber_of_flat A q) (q ⁻¹ᵁ V) hU n het W hgeneric hW

end AlgebraicGeometry.Scheme
