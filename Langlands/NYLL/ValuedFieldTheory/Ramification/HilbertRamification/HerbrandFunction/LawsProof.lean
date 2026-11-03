/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1237, 2026-11-02, with source/interface analysis,
exact-target/helper design and proof-route analysis contributed by
Worker 106: adapt the proofs of M305.006-.011/.013-.014 from upstream
commit fbd320cd8b1b06487c58227e92eb135794267709 and assemble the closed
target UniqueExtensionHerbrandLawsStatement. Prefix namespaces with
Langlands.NYLL and import the published target and generic inverse
proofs. Omit the local Fintype instance: the generic laws need only
`Finite Gal(L/K)`, which Mathlib's existing instances provide under
`[FiniteDimensional K L]`. Retain four independent universes, the
unrestricted evaluations and the finite-dimensional scope of the later six
laws.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.InverseProof

/-!
# Actual unique-extension Herbrand laws: proofs

Adapted from NYLL
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, M305.006-.011 and
M305.013-.014 (lines 88-191). The two evaluations are unrestricted; the
six later laws keep the source hypothesis `[FiniteDimensional K L]`, from
which Mathlib's instance `Finite.algEquiv` (with `instFiniteAlgHomOfFinite`)
makes `Gal(L/K)` finite.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- States the theorem `herbrandFunctionOfUniqueExtension_apply`. -/
@[simp] theorem herbrandFunctionOfUniqueExtension_apply
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (s : ℝ) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s =
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) s :=
  rfl

/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_apply`. -/
@[simp] theorem inverseHerbrandFunctionOfUniqueExtension_apply
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (t : ℝ) :
    inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t =
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) t :=
  rfl

section FiniteDimensional

variable [FiniteDimensional K L]

/-- States the theorem `herbrandFunctionOfUniqueExtension_psi`. -/
@[simp] theorem herbrandFunctionOfUniqueExtension_psi
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (t : ℝ) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq
        (inverseHerbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq t) = t :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_inverseHerbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) t

/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_eta`. -/
@[simp] theorem inverseHerbrandFunctionOfUniqueExtension_eta
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (s : ℝ) :
    inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq
        (herbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq s) = s :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction_herbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) s

/-- States the theorem `herbrandFunctionOfUniqueExtension_strictMono`. -/
theorem herbrandFunctionOfUniqueExtension_strictMono
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) :
    StrictMono (herbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq) :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_strictMono
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq)

/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_strictMono`. -/
theorem inverseHerbrandFunctionOfUniqueExtension_strictMono
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) :
    StrictMono (inverseHerbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq) :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction_strictMono
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq)

/-- States the theorem `upperRamificationGroupOfUniqueExtension_herbrandFunction`. -/
@[simp] theorem upperRamificationGroupOfUniqueExtension_herbrandFunction
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (s : ℝ) :
    upperRamificationGroupOfUniqueExtension
        (base := base) (target := target) huniq
        (herbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq s) =
      lowerRamificationGroup
        (base := base) (target := target) huniq s := by
  exact congrArg
    (lowerRamificationGroup (base := base) (target := target) huniq)
    (inverseHerbrandFunctionOfUniqueExtension_eta
      (base := base) (target := target) huniq s)

open Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
  (inverseHerbrandFunction_mem_Ici_neg_one_iff) in
/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff`. -/
theorem inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) {t : ℝ} :
    -1 ≤ inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t ↔ -1 ≤ t :=
  inverseHerbrandFunction_mem_Ici_neg_one_iff
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq)

end FiniteDimensional

/-- The eight actual unique-extension Herbrand laws M305.006-.011 and
M305.013-.014 at the exact published closed target. -/
theorem uniqueExtensionHerbrandLaws :
    UniqueExtensionHerbrandLawsStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq
  refine ⟨herbrandFunctionOfUniqueExtension_apply huniq,
    inverseHerbrandFunctionOfUniqueExtension_apply huniq, ?_⟩
  intro _
  exact ⟨herbrandFunctionOfUniqueExtension_psi huniq,
    inverseHerbrandFunctionOfUniqueExtension_eta huniq,
    herbrandFunctionOfUniqueExtension_strictMono huniq,
    inverseHerbrandFunctionOfUniqueExtension_strictMono huniq,
    upperRamificationGroupOfUniqueExtension_herbrandFunction huniq,
    fun _ => inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff huniq⟩

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
