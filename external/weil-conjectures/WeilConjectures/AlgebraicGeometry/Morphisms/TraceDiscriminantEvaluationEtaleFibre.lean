/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Discriminant

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineFibreTensorEtale
import WeilConjectures.RingTheory.TraceFormEtaleField

/-!
# Evaluating a trace discriminant on a fibre

## References

* Stacks Project, Tag 0BJF, fibre-algebra argument
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The evaluated discriminant of a finite free affine section algebra is nonzero exactly
when the scheme-theoretic fibre is etale. -/
theorem trace_discriminant_evaluation_ne_zero_iff_etale_fibre
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
      Y.evaluation U.1 y hy (Algebra.discr Γ(Y, U.1) b) ≠ 0 ↔
        Etale (f.fiberToSpecResidueField y) := by
  let := (f.app U.1).hom.toAlgebra
  let := (Y.evaluation U.1 y hy).hom.toAlgebra
  dsimp only
  intro n b
  let := Module.Finite.of_basis b
  let := Module.Free.of_basis b
  let b' := b.baseChange (Y.residueField y)
  have heq : Y.evaluation U.1 y hy (Algebra.discr Γ(Y, U.1) b) =
      Algebra.discr (Y.residueField y) b' := by
    change algebraMap Γ(Y, U.1) (Y.residueField y) _ = _
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, b', Module.Basis.baseChange_apply]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.trace_apply,
      Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  rw [heq, Algebra.discr_def, Algebra.traceMatrix_of_basis,
    ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero,
    Algebra.traceForm_nondegenerate_iff_etale]
  exact (etale_fibre_iff_etale_tensor_section_algebra f U y hy).symm

end AlgebraicGeometry.Scheme
