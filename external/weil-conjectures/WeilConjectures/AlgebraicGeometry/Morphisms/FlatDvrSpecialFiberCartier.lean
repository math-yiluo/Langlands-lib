/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The special fibre of a flat DVR family is an effective Cartier divisor

## References

* Stacks Project, Tag 0EYJ, first paragraph
* Tag 02OO (flat pullback)
* Stacks Project, Tag 0EYJ, first paragraph, and Tag 02OO
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Flatness preserves the nonzerodivisor defining the closed point of a DVR. -/
theorem isEffectiveCartierCenter_specialFiber_of_flat
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Flat q] :
    IsEffectiveCartierCenter (q.fiberι (IsLocalRing.closedPoint A)) := by
  let s := IsLocalRing.closedPoint A
  let i := (Spec (.of A)).fromSpecResidueField s
  let hi : IsClosedImmersion i :=
    isClosed_singleton_iff_isClosedImmersion.mp (IsLocalRing.isClosed_singleton_closedPoint A)
  have hker : i.ker.IsInvertible := by
    apply IdealSheafData.IsInvertible.of_isAffine
    rw [Hom.ker_eq_vanishingIdeal, range_fromSpecResidueField]
    rw [IdealSheafData.vanishingIdeal_ideal]
    change (PrimeSpectrum.vanishingIdeal
      ((isAffineOpen_top (Spec (.of A))).fromSpec ⁻¹' closure {s})).IsRegularPrincipal
    rw [(IsLocalRing.isClosed_singleton_closedPoint A).closure_eq,
      IsAffineOpen.fromSpec_top, isoSpec_Spec_inv]
    have hpre : (Spec.map (ΓSpecIso (.of A)).inv) ⁻¹' {s} =
        {Spec.map (ΓSpecIso (.of A)).hom s} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        have := congrArg (Spec.map (ΓSpecIso (.of A)).hom) hz
        simpa [← Hom.comp_apply, ← Spec.map_comp] using this
      · rintro rfl
        simp [← Hom.comp_apply]
    rw [hpre, PrimeSpectrum.vanishingIdeal_singleton]
    obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hreg : (IsLocalRing.maximalIdeal A).IsRegularPrincipal :=
      ⟨pi, mem_nonZeroDivisors_of_ne_zero hpi.ne_zero,
        (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi⟩
    exact hreg.comap_of_bijective
      (ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.bijective
  let : IsClosedImmersion (q.fiberι s) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst q i))
  apply (isEffectiveCartierCenter_iff_isInvertible_ker).mpr
  change (pullback.fst q i).ker.IsInvertible
  rw [IdealSheafData.ker_fst_of_isClosedImmersion]
  exact hker.comap_of_flat q

end AlgebraicGeometry.Scheme
