/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Discriminant
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatAffineBasis
import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantAffineRestriction
import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionLocalization

/-!
# Gluing local trace discriminants

## References

* Stacks Project, Tag 0BVH, construction preceding Lemma 49.3.1
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem traceDiscriminantSectionIdeal_eq_span
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
      traceDiscriminantSectionIdeal f U = Ideal.span {Algebra.discr Γ(Y, U.1) b} := by
  let := (f.app U.1).hom.toAlgebra
  intro n b
  apply le_antisymm
  · exact (iInf_le_of_le U (iInf_le_of_le le_rfl
      (iInf_le_of_le n (iInf_le_of_le b le_rfl)))).trans_eq (by
        simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
          CommRingCat.hom_id, Ideal.comap_id])
  · refine le_iInf fun V ↦ le_iInf fun h ↦ ?_
    let := (f.app V.1).hom.toAlgebra
    refine le_iInf fun m ↦ le_iInf fun c ↦ ?_
    rw [← Ideal.map_le_iff_le_comap]
    exact (trace_discriminant_span_map_affine_restriction f U V h n m b c).le

/-- Local trace determinants glue to a quasi-coherent ideal. -/
theorem exists_ideal_locally_eq_trace_discriminant_of_finite_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] :
    ∃ J : Y.IdealSheafData, ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      (letI := (f.app U.1).hom.toAlgebra
       ∃ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
         J.ideal U = Ideal.span {Algebra.discr Γ(Y, U.1) b}) := by
  let J : Y.IdealSheafData :=
    { ideal := traceDiscriminantSectionIdeal f
      map_ideal_basicOpen := traceDiscriminantSectionIdeal_map_basicOpen f }
  refine ⟨J, fun y ↦ ?_⟩
  obtain ⟨U, hy, n, ⟨b⟩⟩ := exists_affine_basis_of_finite_flat f y
  refine ⟨U, hy, n, b, ?_⟩
  exact traceDiscriminantSectionIdeal_eq_span f U n b

end AlgebraicGeometry.Scheme
