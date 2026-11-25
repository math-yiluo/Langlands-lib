/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.RingTheory.RegularRingOfQuotientAway

/-!
# The boundary after adjoining the generic point of a regular integral divisor

## References

* Stacks Project, Tag 01WS (local principal nonzerodivisor description)
* Stacks Project, Tag 0EYE, proof
* Tag 00NU
* Tag 0EYJ, trait paragraph
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- At a point on an effective Cartier centre, the stalk map has kernel generated
by a nonzerodivisor in the ambient maximal ideal. -/
private theorem exists_stalk_equation
    {L D : Scheme.{u}} {i : D ⟶ L} (hi : IsEffectiveCartierCenter i) (d : D) :
    ∃ f : L.presheaf.stalk (i d), f ∈ IsLocalRing.maximalIdeal _ ∧
      IsSMulRegular (L.presheaf.stalk (i d)) f ∧
      RingHom.ker (i.stalkMap d).hom = Ideal.span {f} := by
  have : IsClosedImmersion i := hi.isClosedImmersion
  have hinv : i.ker.IsInvertible := isEffectiveCartierCenter_iff_isInvertible_ker.mp hi
  obtain ⟨U, hx, a, ha, hgen⟩ := hinv (i d)
  let V := i ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := U.2.preimage i
  have hd : d ∈ V := hx
  let R := L.presheaf.stalk (i d)
  let S := D.presheaf.stalk d
  let : Algebra Γ(L, U.1) R := L.presheaf.algebra_section_stalk ⟨i d, hx⟩
  let : Algebra Γ(D, V) S := D.presheaf.algebra_section_stalk ⟨d, hd⟩
  let p := (U.2.primeIdealOf ⟨i d, hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨d, hd⟩).asIdeal
  have : IsLocalization.AtPrime R p := U.2.isLocalization_stalk ⟨i d, hx⟩
  have : IsLocalization.AtPrime S q := hV.isLocalization_stalk ⟨d, hd⟩
  have : Module.Flat Γ(L, U.1) R := IsLocalization.flat R p.primeCompl
  let g := (i.app U.1).hom
  have hg : Function.Surjective g := i.app_surjective U.1 U.2
  have hpq : q.comap g = p := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 V hV le_rfl hd
    have happ : i.appLE U.1 V le_rfl = i.app U.1 := by
      dsimp [Scheme.Hom.appLE]
      rw [D.presheaf.map_id (Opposite.op V), Category.comp_id]
    rw [happ] at h
    exact congr($(h).1)
  have hcompl : p.primeCompl.map g = q.primeCompl := by
    simpa only [hpq] using Ideal.map_primeCompl_comap_of_surjective g hg q
  have heq : IsLocalization.map S g (hcompl.symm ▸ p.primeCompl.le_comap_map) =
      (i.stalkMap d).hom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext b
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    exact (i.germ_stalkMap_apply U.1 d hx b).symm
  have hker : RingHom.ker (i.stalkMap d).hom =
      (RingHom.ker g).map (algebraMap Γ(L, U.1) R) := by
    rw [← heq]
    exact IsLocalization.ker_map S g hcompl
  have hgen' : RingHom.ker g = Ideal.span {a} := by
    rw [← i.ker_apply U]
    exact hgen
  let f : R := algebraMap Γ(L, U.1) R a
  have hfker : RingHom.ker (i.stalkMap d).hom = Ideal.span {f} := by
    rw [hker, hgen', Ideal.map_span, Set.image_singleton]
  refine ⟨f, ?_, ?_, hfker⟩
  · apply (IsLocalRing.mem_maximalIdeal f).mpr
    intro hf
    have hfzero : (i.stalkMap d).hom f = 0 :=
      RingHom.mem_ker.mp (hfker ▸ Ideal.mem_span_singleton_self f)
    exact not_isUnit_zero (M₀ := S) (hfzero ▸ hf.map (i.stalkMap d).hom)
  · have hregA : IsSMulRegular Γ(L, U.1) a :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors ha
    exact hregA.of_flat

/-- Removing an open neighbourhood of the generic point leaves a regular boundary
of local dimension at least two. -/
theorem regular_dim_ge_two_outside_divisor_generic_neighbourhood
    {L D : Scheme.{u}} [IsLocallyNoetherian L] [IsRegular D] [IsIntegral D]
    (i : D ⟶ L) (hi : IsEffectiveCartierCenter i)
    (U : L.Opens) (hU : ∀ z : L, z ∈ U ↔ z ∉ Set.range i)
    (W : L.Opens) (hgeneric : i (genericPoint D) ∈ W) :
    ∀ z : L, z ∉ U ⊔ W → IsRegularLocalRing (L.presheaf.stalk z) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk z) := by
  classical
  intro z hz
  have hzU : z ∉ U := fun h ↦ hz (TopologicalSpace.Opens.mem_sup.mpr (Or.inl h))
  have hzW : z ∉ W := fun h ↦ hz (TopologicalSpace.Opens.mem_sup.mpr (Or.inr h))
  have hzi : z ∈ Set.range i := by
    by_contra h
    exact hzU ((hU z).mpr h)
  obtain ⟨d, rfl⟩ := hzi
  have hd : d ≠ genericPoint D := by
    intro h
    exact hzW (h ▸ hgeneric)
  have hdimD : (1 : WithBot ℕ∞) ≤ ringKrullDim (D.presheaf.stalk d) := by
    rw [ringKrullDim_stalk_eq_coheight]
    have hlt : d < (⊤ : D) := by
      refine lt_iff_le_not_ge.mpr ⟨le_top, ?_⟩
      intro h
      exact hd ((Specializes.antisymm (genericPoint_specializes d) h).eq.symm)
    have h := Order.coheight_add_one_le hlt
    simpa using h
  have : IsClosedImmersion i := hi.isClosedImmersion
  obtain ⟨f, hf, hreg, hker⟩ := exists_stalk_equation hi d
  let e := (Ideal.quotEquivOfEq hker.symm).trans
    ((i.stalkMap d).hom.quotientKerEquivOfSurjective (i.stalkMap_surjective d))
  have : IsRegularLocalRing (L.presheaf.stalk (i d) ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  refine ⟨IsRegularLocalRing.of_isRegularLocalRing_quotient _ f hf hreg, ?_⟩
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hf
  rw [← hdim, ringKrullDim_eq_of_ringEquiv e]
  exact (show (2 : WithBot ℕ∞) = 1 + 1 from rfl).le.trans
    (by simpa only [add_comm] using add_le_add_right hdimD 1)

end AlgebraicGeometry.Scheme
