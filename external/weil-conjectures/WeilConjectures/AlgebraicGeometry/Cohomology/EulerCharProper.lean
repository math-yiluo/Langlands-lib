/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing

/-!
# The Euler characteristic of a coherent module on a proper scheme is well defined

For a coherent module `ℱ` on a scheme `X` proper over a field `k`, each `H^q(X, ℱ)` is a
finite-dimensional `k`-vector space and only finitely many of them are nonzero, so
`χ(X, ℱ) = ∑ (-1)^q dim_k H^q(X, ℱ)` is a finite sum of integers.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.finite_setOf_nontrivial_H_of_isProper`: only finitely many
  `H^q(X, ℱ)` are nonzero.
- `AlgebraicGeometry.Scheme.Modules.finite_support_finrankH_of_isProper`: only finitely many
  `h^q(X, ℱ)` are nonzero, so the `finsum` defining `eulerChar` is a finite sum.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

include k in
/-- **Well-definedness of the Euler characteristic.** For a quasi-coherent module `ℱ` on a
scheme proper over a field `k`, only finitely many cohomology groups `H^q(X, ℱ)` are nonzero
(`AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_H_of_isQuasicoherent`). For
coherent `ℱ` each `H^q(X, ℱ)` is moreover finite-dimensional over `k`
(`AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem finite_setOf_nontrivial_H_of_isProper (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    {q : ℕ | Nontrivial (ℱ.H q)}.Finite := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsSeparated (CategoryTheory.Limits.terminal.from X) := by
    rw [← CategoryTheory.Limits.terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  obtain ⟨D, hD'⟩ := exists_forall_subsingleton_H_of_isQuasicoherent (X := X)
  have hD := hD' ℱ
  refine (Set.finite_Iic D).subset fun q hq ↦ ?_
  by_contra h
  have := hD q (not_le.mp h)
  exact not_nontrivial _ hq

/-- **Well-definedness of the Euler characteristic.** For a quasi-coherent module `ℱ` on a
scheme proper over a field `k`, only finitely many of the dimensions `h^q(X, ℱ)` are nonzero, so
the `finsum` defining `χ(X, ℱ) = ∑ (-1)^q h^q(X, ℱ)` is a finite sum. For coherent `ℱ` the
`h^q(X, ℱ)` are the dimensions of finite-dimensional vector spaces
(`AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem finite_support_finrankH_of_isProper (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    (Function.support (ℱ.finrankH k)).Finite := by
  refine (finite_setOf_nontrivial_H_of_isProper k ℱ).subset fun q hq ↦ ?_
  by_contra h
  have : Subsingleton (ℱ.H q) := not_nontrivial_iff_subsingleton.mp h
  exact hq Module.finrank_zero_of_subsingleton

end AlgebraicGeometry.Scheme.Modules
