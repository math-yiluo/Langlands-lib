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
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions

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

open LocalFieldTheory

omit [FiniteDimensional K L] [IsGalois K L] in
def mem_chosenBaseUniformizerPowSubmodule_iffStatement
    (n : Nat) (N : Submodule 𝒪[K] L) (x : L) : Prop :=
    x ∈ chosenBaseUniformizerPowSubmodule K L n N ↔
      ∃ y : L, y ∈ N ∧
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x

omit [FiniteDimensional K L] [IsGalois K L] in
def chosenBaseUniformizerPow_mul_mem_monoStatement
    {M : Submodule 𝒪[K] L} {m n : Nat} {x : L} (hmn : m ≤ n)
    (hx : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x ∈ M) : Prop :=
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M

omit [FiniteDimensional K L] [IsGalois K L] in
def chosenBaseUniformizerPowSubmodule_antitoneStatement
    (N : Submodule 𝒪[K] L) {m n : Nat} (hmn : m ≤ n) : Prop :=
    chosenBaseUniformizerPowSubmodule K L n N ≤
      chosenBaseUniformizerPowSubmodule K L m N

omit [FiniteDimensional K L] [IsGalois K L] in
def chosenBaseUniformizerPowSubmodule_succ_leStatement
    (n : Nat) (N : Submodule 𝒪[K] L) : Prop :=
    chosenBaseUniformizerPowSubmodule K L (n + 1) N ≤
      chosenBaseUniformizerPowSubmodule K L n N

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_topStatement
    {M : Submodule 𝒪[K] L}
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) (x : L) : Prop :=
    ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_topStatement
    {M N : Submodule 𝒪[K] L} (hN : N.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) : Prop :=
    ∃ n : Nat, chosenBaseUniformizerPowSubmodule K L n N ≤ M

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_topStatement
    {M N P : Submodule 𝒪[K] L} (hN : N.FG) (hP : P.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) : Prop :=
    ∃ n : Nat, ∀ x : L, x ∈ N → ∀ y : L, y ∈ P →
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_topStatement
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n M →
      ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
        x * y ∈ chosenBaseUniformizerPowSubmodule K L n M

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_topStatement
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n M →
      ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
        x * y ∈ chosenBaseUniformizerPowSubmodule K L (n + 1) M

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_selfStatement : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succStatement : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L)

omit [FiniteDimensional K L] [IsGalois K L] in
def chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_leStatement
    {N M : Submodule 𝒪[K] L} {a n : Nat}
    (h : chosenBaseUniformizerPowSubmodule K L a N ≤ M) : Prop :=
    chosenBaseUniformizerPowSubmodule K L (a + n) N ≤
      chosenBaseUniformizerPowSubmodule K L n M

end
end Langlands.NYLL.CyclicCohomology
