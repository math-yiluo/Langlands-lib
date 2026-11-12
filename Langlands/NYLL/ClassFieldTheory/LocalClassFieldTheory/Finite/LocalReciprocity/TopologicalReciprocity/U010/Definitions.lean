/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 9 November 2026: extract M257.010 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
TopologicalReciprocity.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Prefix the namespace with Langlands.NYLL and remove all NYLL imports.
Replace the private M257.009 closure helper by Mathlib IsClosed.closure_eq
and isClosed_discrete, using the same equality and quotient equivalence.
Preserve the original section telescope. LICENSE and NOTICE: licenses/NYLL/.
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.NumberTheory.LocalField.Basic

/-! # Comparison of finite Galois abelianizations -/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- For a finite-dimensional Galois extension, algebraic and topological
abelianization agree as multiplicative groups. -/
noncomputable def topologicalAbelianization_finite_equiv :
    Abelianization (Gal(L / K)) ≃* TopologicalAbelianization (Gal(L / K)) := by
  let h : Subgroup.topologicalClosure (commutator (Gal(L / K))) =
      commutator (Gal(L / K)) :=
    SetLike.coe_injective
      (isClosed_discrete (commutator (Gal(L / K)) : Set (Gal(L / K)))).closure_eq
  exact QuotientGroup.quotientMulEquivOfEq h.symm

end Langlands.NYLL.LocalClassFieldTheory
