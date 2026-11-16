/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M144.122 from
Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 2162–2191. Add the
Langlands.NYLL namespace prefix, keep the source section variables and `omit`
line, and give the theorem the published target applied to its parameters as
its type, unfolded at the start of the proof. The source tactics are otherwise
unchanged; the published `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff`
is used through its reverse direction exactly as in the source. Import the
target module and the published proof of that theorem instead of the source
imports. Omit the source noncomputable section and all other source
declarations. See the paired Markdown; the original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U103.Proofs

universe u

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Principal units from the next level lie in the kernel of the lattice-class
homomorphism. -/
theorem chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u : Vn) (hu : (u : 𝒪[L]ˣ) ∈ Vsucc) :
    chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement
      K L hVn hVsucc hmul_error u hu := by
  unfold chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement
  rw [MonoidHom.mem_ker]
  have hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    exact hVn ▸ u.2
  have hu_succ : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
    exact hVsucc ▸ hu
  have hzero :
      chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 :=
    (chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff
      (K := K) (L := L) (u : 𝒪[L]ˣ) hu_n).2 hu_succ
  change Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n) = 1
  simpa using congrArg Multiplicative.ofAdd hzero

end Langlands.NYLL.CyclicCohomology
