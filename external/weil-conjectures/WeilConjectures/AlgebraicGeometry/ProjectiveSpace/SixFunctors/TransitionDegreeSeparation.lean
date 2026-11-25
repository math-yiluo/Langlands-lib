/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.OverlapLaurentCoordinates
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Transition exponents are invariant under changes of chart frames

## References

* Stacks Project, Tag 0BXJ, proof
* Stacks Project, Tag 0BXJ, uniqueness in its Picard
  classification, specialized to dimension one over a field
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

private theorem chart_unit_constant (k : Type u) [Field k]
    (i : ULift.{u} (Fin 2))
    (a : Γ(ProjectiveLine (Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ) :
    ∃ c : k, c ≠ 0 ∧ a.val = chartConst k _ c := by
  let r := polyEquivChart k (ne_other i)
  let ρ := (ProjectiveLine (Spec (.of k))).presheaf.mapIso
    (eqToIso (chart_singleton k i)).op
  let w := Units.map ρ.hom.hom.toMonoidHom a
  obtain ⟨c, hc, h⟩ := Polynomial.isUnit_iff.mp (w.isUnit.map r.symm.toRingHom)
  change Polynomial.C c = r.symm w.val at h
  have hr : r (Polynomial.C c) = chartConst k (chart k {i}) c := by
    simp only [r, polyEquivChart_apply, polyToChart, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
  refine ⟨c, hc.ne_zero, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ρ.hom).1
  have hw : ρ.hom a.val = chartConst k (chart k {i}) c := by
    change w.val = _
    rw [← r.apply_symm_apply w.val, ← h, hr]
  rw [hw]
  change _ = (ProjectiveLine (Spec (.of k))).presheaf.map
    (eqToHom (chart_singleton k i)).op (chartConst k _ c)
  rw [Subsingleton.elim (eqToHom (chart_singleton k i))
    (homOfLE (chart_singleton k i).le)]
  exact (presheaf_map_chartConst k (chart_singleton k i).le c).symm

/-- Standard transitions of different degrees are not related by chart units. -/
theorem eq_degree_of_chart_units (k : Type u) [Field k] (d e : ℤ)
    (a : Γ(ProjectiveLine (Spec (.of k)),
      standardOpen _ (Spec (.of k)) (⟨0⟩ : ULift.{u} (Fin 2)))ˣ)
    (b : Γ(ProjectiveLine (Spec (.of k)),
      standardOpen _ (Spec (.of k)) (⟨1⟩ : ULift.{u} (Fin 2)))ˣ)
    (h : Units.map ((ProjectiveLine (Spec (.of k))).presheaf.map
        (homOfLE inf_le_left).op).hom.toMonoidHom a *
          transitionUnit (ULift.{u} (Fin 2)) (Spec (.of k)) d ⟨0⟩ ⟨1⟩ =
        transitionUnit (ULift.{u} (Fin 2)) (Spec (.of k)) e ⟨0⟩ ⟨1⟩ *
          Units.map ((ProjectiveLine (Spec (.of k))).presheaf.map
            (homOfLE inf_le_right).op).hom.toMonoidHom b) : d = e := by
  let S := Spec (.of k)
  let U₀ := standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩
  let U₁ := standardOpen (ULift.{u} (Fin 2)) S ⟨1⟩
  obtain ⟨c₀, hc₀, ha⟩ := chart_unit_constant k ⟨0⟩ a
  obtain ⟨c₁, hc₁, hb⟩ := chart_unit_constant k ⟨1⟩ b
  have hval := congrArg Units.val h
  change (ProjectiveLine S).presheaf.map (homOfLE inf_le_left).op a.val *
      (ratioUnit (ULift.{u} (Fin 2)) S ⟨0⟩ ⟨1⟩ ^ d).val =
    (ratioUnit (ULift.{u} (Fin 2)) S ⟨0⟩ ⟨1⟩ ^ e).val *
      (ProjectiveLine S).presheaf.map (homOfLE inf_le_right).op b.val at hval
  rw [ha, hb, presheaf_map_chartConst, presheaf_map_chartConst, mul_comm _
    (chartConst k (U₀ ⊓ U₁) c₁)] at hval
  have hp : LaurentPolynomial.C c₀ * LaurentPolynomial.T d =
      LaurentPolynomial.C c₁ * LaurentPolynomial.T e := by
    apply (bijective_overlap_laurent k).1
    simpa only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T] using hval
  have hd := congrArg LaurentPolynomial.degree hp
  rw [LaurentPolynomial.degree_C_mul_T d c₀ hc₀,
    LaurentPolynomial.degree_C_mul_T e c₁ hc₁] at hd
  exact WithBot.coe_injective hd

end AlgebraicGeometry.ProjectiveLine
