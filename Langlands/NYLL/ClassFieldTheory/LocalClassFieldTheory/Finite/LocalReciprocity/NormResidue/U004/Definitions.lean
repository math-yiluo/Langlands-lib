/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 10 November 2026: focused extraction from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean at fbd320cd8b1b06487c58227e92eb135794267709;
add Langlands.NYLL to the namespace and replace the full NYLL import by
its published focused prerequisite. Retain source parameters and construction.
LICENSE and NOTICE: licenses/NYLL/.
-/

import Mathlib.GroupTheory.Abelianization.Defs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U010.Definitions
import Mathlib.FieldTheory.Galois.Abelian

/-! # Topological abelianization of a finite abelian Galois group -/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- For a finite abelian Galois extension, topological abelianization is
canonically homeomorphic to the actual Galois group. -/
noncomputable def topologicalAbelianizationEquivSelf :
    TopologicalAbelianization Gal(L / K) ≃ₜ* Gal(L / K) := by
  letI : DiscreteTopology (TopologicalAbelianization Gal(L / K)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let e : TopologicalAbelianization Gal(L / K) ≃* Gal(L / K) :=
    (topologicalAbelianization_finite_equiv K L).symm.trans
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

end Langlands.NYLL.LocalClassFieldTheory
