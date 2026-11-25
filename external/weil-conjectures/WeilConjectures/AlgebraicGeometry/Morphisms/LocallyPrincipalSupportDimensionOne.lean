/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.RingTheory.Spectrum.Prime.LTSeries

/-!
# Dimension-one detection in a locally principal closed set

## References

* Stacks Project, Tag 0BJG
* Stacks Project, with the passage from local rings to schemes in Tag 0BJH
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- Every positive-dimensional point of a locally principal closed set has a
local-dimension-one generalization in that closed set. -/
theorem exists_dimension_one_generalization_in_locallyPrincipal_support
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (J : Y.IdealSheafData)
    (hJ : J.IsLocallyPrincipal) (y : Y) (hy : y ∈ J.support)
    (hpos : (0 : WithBot ℕ∞) < ringKrullDim (Y.presheaf.stalk y)) :
    ∃ y' : Y, Specializes y' y ∧ y' ∈ J.support ∧
      ringKrullDim (Y.presheaf.stalk y') = 1 := by
  obtain ⟨U, hyU, ⟨d, hd⟩⟩ := hJ y
  have hU : IsAffineOpen U.1 := U.2
  let p := hU.primeIdealOf ⟨y, hyU⟩
  let : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyU⟩ : U.1)
  let := hU.isLocalization_stalk ⟨y, hyU⟩
  have hdim : ringKrullDim (Y.presheaf.stalk y) = (p.asIdeal.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Y.presheaf.stalk y)
  have hheight : 0 < p.asIdeal.height := by
    rw [hdim] at hpos
    exact_mod_cast hpos
  have hdmem : d ∈ p.asIdeal := by
    have hz := (IdealSheafData.mem_support_iff_of_mem hyU).mp hy
    have heq : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
    rw [← heq] at hz
    change p ∈ hU.fromSpec ⁻¹' Y.zeroLocus (U := U.1) (J.ideal U : Set Γ(Y, U.1)) at hz
    rw [hU.fromSpec_preimage_zeroLocus] at hz
    exact hz (by rw [hd]; exact Submodule.mem_span_singleton_self d)
  -- Reorder a longest chain so that its height-one prime contains the generator.
  obtain ⟨c, hlast, hlength⟩ := p.asIdeal.exists_ltSeries_length_eq_height
  change c.last = p at hlast
  obtain ⟨q, hdq, hlen, -, hqend⟩ :=
    PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last c (by rw [hlast]; exact hdmem)
  have hqpos : 0 < q.length := by
    have : (0 : ℕ∞) < c.length := hlength ▸ hheight
    exact hlen ▸ (by exact_mod_cast this)
  have hqheight : Order.height q.last = q.length := by
    rw [← hqend, hlast, ← PrimeSpectrum.height_eq_orderHeight, ← hlength, hlen]
  have hqone : (q 1).asIdeal.height = 1 := by
    rw [PrimeSpectrum.height_eq_orderHeight]
    have h := Order.height_eq_index_of_length_eq_height_last hqheight.symm
      (1 : Fin (q.length + 1))
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < q.length + 1)] using h
  have hqp : q 1 ≤ p := by
    rw [← hlast, hqend]
    exact q.monotone (Fin.le_last _)
  have hqU : hU.fromSpec (q 1) ∈ U.1 :=
    hU.range_fromSpec.subset (Set.mem_range_self (q 1))
  refine ⟨hU.fromSpec (q 1), ?_, ?_, ?_⟩
  · have heq : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
    rw [← heq]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hqp).map hU.fromSpec.continuous
  · apply (IdealSheafData.mem_support_iff_of_mem hqU).mpr
    change q 1 ∈ hU.fromSpec ⁻¹' Y.zeroLocus (U := U.1) (J.ideal U : Set Γ(Y, U.1))
    rw [hU.fromSpec_preimage_zeroLocus]
    rw [hd, Ideal.submodule_span_eq]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hdq)
  · let := TopCat.Presheaf.algebra_section_stalk Y.presheaf
      (⟨hU.fromSpec (q 1), hqU⟩ : U.1)
    let := hU.isLocalization_stalk' (q 1) hqU
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q 1).asIdeal, hqone]
    rfl

end AlgebraicGeometry.Scheme
