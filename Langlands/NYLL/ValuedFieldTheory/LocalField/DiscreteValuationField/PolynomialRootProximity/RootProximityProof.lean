/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-
Modified by Worker 576, 14 November 2026: port M395.002 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709 to the exact closed Library target;
qualify the theorem namespace with Langlands.NYLL and replace the source's
private helper with the separately published Langlands.NYLL.PortInternal.M395.d001.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity.MultisetProductComparison
import Mathlib.Data.Finset.Max

open scoped Polynomial

universe u

namespace Langlands.NYLL.Polynomial.Splits

/-- The exact DVR root-proximity statement, with repeated roots allowed. -/
theorem exists_root_addVal_eval_le_sub_add_derivative :
    exists_root_addVal_eval_le_sub_add_derivativeStatement.{u} := by
  intro R _ _ _ p hs hm hdeg x
  classical
  have hroots : p.roots ≠ 0 := by
    intro hzero
    apply hdeg
    simpa [hzero] using hs.natDegree_eq_card_roots
  obtain ⟨y, hy, hymax⟩ :=
    Multiset.exists_max_image
      (s := p.roots)
      (fun z => IsDiscreteValuationRing.addVal R (x - z)) hroots
  have hfactor :
      ∀ z ∈ p.roots.erase y,
        IsDiscreteValuationRing.addVal R (x - z) ≤
          IsDiscreteValuationRing.addVal R (y - z) := by
    intro z hz
    have hzroot : z ∈ p.roots :=
      Multiset.mem_of_mem_erase hz
    have hmax :
        IsDiscreteValuationRing.addVal R (x - z) ≤
          IsDiscreteValuationRing.addVal R (x - y) :=
      hymax z hzroot
    have hneg :
        IsDiscreteValuationRing.addVal R (y - x) =
          IsDiscreteValuationRing.addVal R (x - y) := by
      have hsub : y - x = -(x - y) := by ring
      rw [hsub, (IsDiscreteValuationRing.addVal R).map_neg]
    have hmax' :
        IsDiscreteValuationRing.addVal R (x - z) ≤
          IsDiscreteValuationRing.addVal R (y - x) := by
      rw [hneg]
      exact hmax
    have hultra :=
      IsDiscreteValuationRing.addVal_add
        (R := R) (a := y - x) (b := x - z)
    have hsum : (y - x) + (x - z) = y - z := by
      ring
    rw [min_eq_right hmax', hsum] at hultra
    exact hultra
  have hprod :
      IsDiscreteValuationRing.addVal R
          (((p.roots.erase y).map (x - ·)).prod) ≤
        IsDiscreteValuationRing.addVal R
          (((p.roots.erase y).map (y - ·)).prod) :=
    Langlands.NYLL.PortInternal.M395.d001 (p.roots.erase y)
      (x - ·) (y - ·) hfactor
  have hroot_prod :
      ((p.roots.map (x - ·)).prod) =
        (x - y) * (((p.roots.erase y).map (x - ·)).prod) := by
    calc
      ((p.roots.map (x - ·)).prod) =
          (((y ::ₘ p.roots.erase y).map (x - ·)).prod) :=
        congrArg (fun s : Multiset R => (s.map (x - ·)).prod)
          (Multiset.cons_erase hy).symm
      _ = (x - y) * (((p.roots.erase y).map (x - ·)).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]
  refine ⟨y, hy, ?_⟩
  calc
    IsDiscreteValuationRing.addVal R (p.eval x) =
        IsDiscreteValuationRing.addVal R
          ((p.roots.map (x - ·)).prod) := by
            rw [hs.eval_eq_prod_roots_of_monic hm]
    _ =
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R
            (((p.roots.erase y).map (x - ·)).prod) := by
              rw [hroot_prod, IsDiscreteValuationRing.addVal_mul]
    _ ≤
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R
            (((p.roots.erase y).map (y - ·)).prod) :=
      add_le_add (le_refl _) hprod
    _ =
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R
            (p.derivative.eval y) := by
              rw [hs.eval_root_derivative hm hy]

end Langlands.NYLL.Polynomial.Splits
