/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 643: extract M144.071 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace, imports and exact target.
The unpublished M144.034 geometric identity is derived under a private name.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.U069.Proofs
import Mathlib.Algebra.Ring.GeomSum

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory Filter
open scoped ValuativeRel

universe u

private theorem normalBasisInverseCorrectionProductIdentity
    {F : Type u} [Field F] (x : F) (d : Nat) :
    (1 + x) * (1 + inverseCorrectionPartialSum (L := F) x d) =
      1 - (-x) ^ (d + 1) := by
  have hsum : 1 + inverseCorrectionPartialSum (L := F) x d =
      (Finset.range (d + 1)).sum fun i => (-x) ^ i := by
    induction d with
    | zero => simp [inverseCorrectionPartialSum]
    | succ d ih =>
      have hsucc : inverseCorrectionPartialSum (L := F) x (d + 1) =
          inverseCorrectionPartialSum (L := F) x d + (-x) ^ (d + 1) := by
        simp [inverseCorrectionPartialSum, Finset.sum_range_succ]
      rw [hsucc, Finset.sum_range_succ, ← ih]
      simp [add_assoc]
  rw [hsum]
  simpa [sub_neg_eq_add] using (mul_neg_geom_sum (x := (-x : F)) (n := d + 1))

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- Products with finite inverse corrections tend to one. -/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_oneStatement K L hle hu := by
  let x𝒪 : 𝒪[L] := (u : 𝒪[L]) - 1
  let x : L := (x𝒪 : L)
  have hres𝒪 :
      Tendsto (fun d : Nat => (-x𝒪) ^ (d + 1)) atTop (nhds (0 : 𝒪[L])) := by
    exact chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero K L hle hu
  have hresL :
      Tendsto (fun d : Nat => ((((-x𝒪) ^ (d + 1) : 𝒪[L]) : L)))
        atTop (nhds (0 : L)) :=
    (continuous_subtype_val.tendsto (0 : 𝒪[L])).comp hres𝒪
  have htarget :
      Tendsto (fun d : Nat => (1 : L) - ((((-x𝒪) ^ (d + 1) : 𝒪[L]) : L)))
        atTop (nhds (1 : L)) := by
    simpa using (tendsto_const_nhds (x := (1 : L))).sub hresL
  refine htarget.congr' (Eventually.of_forall ?_)
  intro d
  have hgeom :
      (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) =
        1 - (-x) ^ (d + 1) :=
    normalBasisInverseCorrectionProductIdentity x d
  have hu_eq : 1 + x = (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    simp [x, x𝒪]
  simpa [x, x𝒪, hu_eq] using hgeom.symm

end Langlands.NYLL.CyclicCohomology
