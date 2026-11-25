/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Discriminant

import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantEvaluationEtaleFibre
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods

/-!
# Local trace discriminants detect non-etale fibres

## References

* Stacks Project, Tag 0BVH, Lemma 49.3.1
* Stacks Project, Tag 0BVH, Lemma 49.3.1, and its finite flat fibre criterion
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- On a free affine chart, the trace determinant vanishes precisely over a non-etale point. -/
theorem trace_discriminant_zeroLocus_iff_nonEtale_fibre
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
      y ∈ Y.zeroLocus {Algebra.discr Γ(Y, U.1) b} ↔
        ∃ x : X, f x = y ∧ ¬ (∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) := by
  classical
  let := (f.app U.1).hom.toAlgebra
  dsimp only
  intro n b
  have heval := trace_discriminant_evaluation_ne_zero_iff_etale_fibre f U y hy n b
  have hzero : y ∈ Y.zeroLocus {Algebra.discr Γ(Y, U.1) b} ↔
      Y.evaluation U.1 y hy (Algebra.discr Γ(Y, U.1) b) = 0 := by
    rw [Y.zeroLocus_singleton]
    exact (Y.evaluation_eq_zero_iff_notMem_basicOpen y hy _).symm
  rw [hzero]
  constructor
  · intro hz
    by_contra h
    push Not at h
    have hE := (etale_fibre_iff_forall_etale_neighbourhood f y).mpr h
    exact (heval.mpr hE) hz
  · rintro ⟨x, hxy, hx⟩
    by_contra hz
    have hE := heval.mp hz
    exact hx ((etale_fibre_iff_forall_etale_neighbourhood f y).mp hE x hxy)

end AlgebraicGeometry.Scheme
