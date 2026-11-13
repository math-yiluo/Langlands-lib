/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 64, 13 November 2026: prove the published M257.006
target from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/
LocalReciprocity/TopologicalReciprocity.lean at
fbd320cd8b1b06487c58227e92eb135794267709 under the inventory name
Langlands.NYLL.PortInternal.M257.d006. The theorem telescope is the
source's; the source proof (compact integer-unit norms and finiteness of
the norm quotient from local reciprocity) is replaced by a new proof: the
one-variable inverse function theorem applied to t ↦ N(1 + t • y) for an
element y of nonzero trace. LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Statements
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Polynomial Filter Topology

/-! # Openness of the norm subgroup with compatible local-field structures -/

namespace Langlands.NYLL.PortInternal.M257

/-- The norm subgroup `N_{L/K}(Lˣ)` is open in `Kˣ`. The polynomial
`t ↦ N(1 + t • y)` has derivative `Tr(y) ≠ 0` at `0`, so by the inverse function
theorem over the complete field `K` its values fill a neighbourhood of `1`. -/
theorem d006
    (K L : Type)
    [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]
    [CompleteSpace K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    d006Statement K L := by
  classical
  unfold d006Statement
  -- an element with nonzero trace
  obtain ⟨y, hy⟩ : ∃ y : L, Algebra.trace K L y ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero K L (LinearMap.ext h)
  -- the polynomial `t ↦ N(1 + t y)`
  let b := Module.finBasis K L
  let M := Algebra.leftMulMatrix b y
  obtain ⟨Q, hQ⟩ : ∃ Q : K[X], Q = Matrix.det (1 + (X : K[X]) • M.map C) := ⟨_, rfl⟩
  have hQeval : ∀ t : K, Q.eval t = Algebra.norm K (1 + t • y) := by
    intro t
    rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, hQ,
      ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, map_add, coe_evalRingHom, Matrix.one_apply, M]
    split_ifs <;> simp <;> ring
  have hderiv : HasStrictDerivAt (fun t : K => Q.eval t) (Algebra.trace K L y) 0 := by
    have h := Q.hasStrictDerivAt 0
    have h2 : Q.derivative.eval 0 = Algebra.trace K L y := by
      rw [Algebra.trace_eq_matrix_trace b, hQ]
      exact Matrix.derivative_det_one_add_X_smul M
    rwa [h2] at h
  have hQ0 : Q.eval 0 = 1 := by
    rw [hQeval, zero_smul, add_zero, map_one]
  -- the range of `t ↦ N(1 + t y)` is a neighbourhood of `1` in `K`
  have hrange : Set.range (fun t : K => Q.eval t) ∈ 𝓝 (1 : K) := by
    have h := hderiv.map_nhds_eq hy
    rw [hQ0] at h
    rw [← h]
    exact Filter.range_mem_map
  -- its preimage in `Kˣ` is a neighbourhood of `1` contained in the norm subgroup
  have hnhds : (localNormSubgroup K L : Set Kˣ) ∈ 𝓝 (1 : Kˣ) := by
    have hpre : (Units.val ⁻¹' Set.range (fun t : K => Q.eval t) : Set Kˣ) ∈ 𝓝 (1 : Kˣ) :=
      Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using hrange)
    refine Filter.mem_of_superset hpre ?_
    rintro u ⟨t, ht⟩
    have hnorm : Algebra.norm K (1 + t • y) = (u : K) := by
      rw [← hQeval]; exact ht
    have hz : (1 + t • y : L) ≠ 0 := by
      intro hz
      rw [hz, Algebra.norm_zero] at hnorm
      exact u.ne_zero hnorm.symm
    refine ⟨Units.mk0 _ hz, ?_⟩
    apply Units.ext
    simp only [normUnits, Units.coe_map, Units.val_mk0]
    exact hnorm
  exact Subgroup.isOpen_of_mem_nhds _ hnhds

end Langlands.NYLL.PortInternal.M257
