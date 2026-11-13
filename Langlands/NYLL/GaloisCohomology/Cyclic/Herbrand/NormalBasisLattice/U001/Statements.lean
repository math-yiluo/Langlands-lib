/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted the listed theorem types
as Prop-valued definitions, removed their proofs, prefixed the namespace
with Langlands.NYLL and reduced imports. See the paired source map.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

set_option linter.unusedVariables false

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def normalBasisConjugates_span_eq_topStatement : Prop :=
    Submodule.span K
        (Set.range (fun σ : Gal(L/K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L/K))))) = ⊤

def chosenNormalBasisIntegerLattice_eq_spanStatement : Prop :=
    chosenNormalBasisIntegerLattice K L =
      Submodule.span 𝒪[K]
        (Set.range (fun σ : Gal(L/K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L/K)))))

def normalBasis_mem_integerLatticeStatement (σ : Gal(L/K)) : Prop :=
    IsGalois.normalBasis K L σ ∈ chosenNormalBasisIntegerLattice K L

def chosenNormalBasisIntegerLattice_field_span_eq_topStatement : Prop :=
    Submodule.span K ((chosenNormalBasisIntegerLattice K L : Submodule 𝒪[K] L) : Set L) =
      ⊤

def galoisGroup_apply_mem_chosenNormalBasisIntegerLatticeStatement
    (τ : Gal(L/K)) {x : L}
    (hx : x ∈ chosenNormalBasisIntegerLattice K L) : Prop :=
    τ x ∈ chosenNormalBasisIntegerLattice K L

def chosenNormalBasisIntegerLattice_fgStatement : Prop :=
    (chosenNormalBasisIntegerLattice K L).FG

end
end Langlands.NYLL.CyclicCohomology
