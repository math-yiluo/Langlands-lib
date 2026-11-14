/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 642 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
NormalBasisLattice.lean, lines 1117–1146. Namespace and imports are adapted;
the theorem is typed against the published Prop target. See the paired Markdown
for proof modifications. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.Statements
import Mathlib.Tactic.Ring

namespace Langlands.NYLL.CyclicCohomology

open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]

private theorem unitProductSubOne_local (a b : 𝒪[L]ˣ) :
    ((a * b : 𝒪[L]ˣ) : 𝒪[L]) - 1 =
      ((a : 𝒪[L]) - 1) * ((b : 𝒪[L]) - 1) +
        ((a : 𝒪[L]) - 1) + ((b : 𝒪[L]) - 1) := by
  simp only [Units.val_mul]
  ring

theorem chosenNormalBasisPrincipalUnitSet_mul_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u v : 𝒪[L]ˣ}
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_mul_memStatement K L hmul hu hv := by
  let E : Submodule 𝒪[K] L :=
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  let x : L := ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  let y : L := ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hx : x ∈ E := hu
  have hy : y ∈ E := hv
  have hxy : x * y ∈ E := hmul x hx y hy
  have hsum : x * y + x + y ∈ E := E.add_mem (E.add_mem hxy hx) hy
  have hunit :
      ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = x * y + x + y := by
    have h := congrArg (fun z : 𝒪[L] => (z : L)) (unitProductSubOne_local L u v)
    simpa [x, y, map_add, map_mul] using h
  change ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈ E
  rw [hunit]
  exact hsum

end Langlands.NYLL.CyclicCohomology
