/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.Definitions

/-!
# Target: the next principal-unit level lies in the kernel

Modified by Worker 5264, 15 November 2026: state the source theorem M144.122
`chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition with the source section variables and `omit` line. Prefix the
namespace with `Langlands.NYLL`, append `Statement` to the name, omit the
proof and the rest of the source file, and import the module of this port
that defines `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom` instead of
the source imports. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/


universe u

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
set_option linter.unusedVariables false in
/-- Target: principal units from the next level lie in the kernel of the
lattice-class homomorphism. -/
def chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement
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
    (u : Vn) (hu : (u : 𝒪[L]ˣ) ∈ Vsucc) : Prop :=
    u ∈ (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom
      K L n hVn hmul_error).ker

end

end Langlands.NYLL.CyclicCohomology
