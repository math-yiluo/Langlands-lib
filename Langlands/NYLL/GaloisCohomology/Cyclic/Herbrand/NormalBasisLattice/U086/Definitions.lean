/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 232 from the NYLL pinned source units listed in the paired Markdown.
The namespace and imports are adapted. Source data bodies are unchanged;
source theorems are replaced by exact Prop-valued definitions.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

def chosenNormalBasisLatticeSuccSubmodule (n : Nat) :
    Submodule 𝒪[K]
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :=
  (chosenBaseUniformizerPowSubmodule K L (n + 1)
    (chosenNormalBasisIntegerLattice K L)).submoduleOf
      (chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L))

def chosenNormalBasisLatticeSuccQuot (n : Nat) : Type u :=
  (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
    chosenNormalBasisLatticeSuccSubmodule K L n

instance chosenNormalBasisLatticeSuccQuotAddCommGroup (n : Nat) :
    AddCommGroup (chosenNormalBasisLatticeSuccQuot K L n) := by
  change AddCommGroup
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n)
  infer_instance

instance chosenNormalBasisLatticeSuccQuotModule (n : Nat) :
    Module 𝒪[K] (chosenNormalBasisLatticeSuccQuot K L n) := by
  change Module 𝒪[K]
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n)
  infer_instance

def chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) := by
  change
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) ≃ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n)
  exact LinearEquiv.refl 𝒪[K] _

def chosenNormalBasisLatticeSuccQuotMk (n : Nat) :
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →ₗ[𝒪[K]]
      chosenNormalBasisLatticeSuccQuot K L n := by
  change
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n)
  exact (chosenNormalBasisLatticeSuccSubmodule K L n).mkQ

end

end Langlands.NYLL.CyclicCohomology
