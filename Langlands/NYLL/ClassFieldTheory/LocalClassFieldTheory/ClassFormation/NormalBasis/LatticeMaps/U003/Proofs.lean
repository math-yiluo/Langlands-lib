/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M152.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 55–65. Add the Langlands.NYLL
namespace prefix, keep the source section variables, give the theorem the
published target applied to its parameters as its type and omit the `@[simp]`
attribute. The source `simp` call does not close the goal here, because the
equality proof inside the basis definition has a Statement type; it is
replaced by a term-mode application of Mathlib's
`Module.Basis.restrictScalars_apply`, which matches by unfolding the basis
definition. Import only the target module. Omit the source noncomputable
section and all other source declarations. See the paired Markdown; the
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Statements

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The integral lattice basis has the same underlying vectors as the chosen
normal basis. -/
theorem chosenNormalBasisIntegerLatticeBasis_apply (σ : Gal(L/K)) :
    chosenNormalBasisIntegerLatticeBasis_applyStatement K L σ :=
  Module.Basis.restrictScalars_apply 𝒪[K] (IsGalois.normalBasis K L) σ

end Langlands.NYLL.LocalClassFieldTheory
