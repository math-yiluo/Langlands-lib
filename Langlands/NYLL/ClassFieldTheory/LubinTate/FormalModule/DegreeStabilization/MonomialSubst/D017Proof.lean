/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 224, 2026-11-16: extract the proof of the source-private
M351.017 at upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
state it as d017 with the exact published d017Statement target; replace the
source-private linear model by published d011; qualify the opened namespaces
with Langlands.NYLL; and import focused published modules. Include private
proofs of the unpublished order and linear-model prerequisites under fresh
names, retaining their source proofs. Omit the unused Fintype section instance,
retain Finite and the independent universes u, v, w, and unfold the target
before the source proof. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.LinearStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.ConstantCoeffInVariable
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Monomial substitution agrees with the linear model below the next degree

Proof of NYLL M351.017, with private prerequisite proofs. The difference
between substituting ebar(X_i) and π X_i into c X^d has order at least |d| + 1.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

private theorem order_pow_for_d017
    {R : Type*} [CommRing R] {τ : Type*}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    (n : ℕ∞) ≤ (f ^ n).order := by
  calc
    (n : ℕ∞) = n • (1 : ℕ∞) := by rw [nsmul_eq_mul, mul_one]
    _ ≤ n • f.order := nsmul_le_nsmul_right hf n
    _ ≤ (f ^ n).order := MvPowerSeries.le_order_pow n

private theorem order_sum_for_d017
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (h : ∀ i ∈ s, m ≤ (f i).order) :
    m ≤ (∑ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, MvPowerSeries.order_zero]
      exact le_top
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (le_min
          (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans
        MvPowerSeries.min_order_le_add

private theorem order_prod_pow_for_d017
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, (f i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Nat.cast_zero]
      exact bot_le
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        ((n i + ∑ j ∈ s, n j : ℕ) : ℕ∞) =
            (n i : ℕ∞) + ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
          norm_cast
        _ ≤ ((f i) ^ n i).order +
            (∏ j ∈ s, (f j) ^ n j).order :=
          add_le_add
            (order_pow_for_d017
              (f i) (n i) (hf i (Finset.mem_insert_self i s)))
            (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ ((f i) ^ n i * ∏ j ∈ s, (f j) ^ n j).order :=
          MvPowerSeries.le_order_mul

private theorem order_pow_sub_for_d017
    {R : Type*} [CommRing R] {τ : Type*}
    (f g : MvPowerSeries τ R)
    (hf : (1 : ℕ∞) ≤ f.order)
    (hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) :
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
      (f ^ n - g ^ n).order := by
  let q :=
    ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hq : ((n - 1 : ℕ) : ℕ∞) ≤ q.order := by
    apply order_sum_for_d017
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    calc
      ((n - 1 : ℕ) : ℕ∞) =
          (i : ℕ∞) + ((n - 1 - i : ℕ) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (f ^ i).order + (g ^ (n - 1 - i)).order :=
        add_le_add
          (order_pow_for_d017 f i hf)
          (order_pow_for_d017
            g (n - 1 - i) hg)
      _ ≤ (f ^ i * g ^ (n - 1 - i)).order :=
        MvPowerSeries.le_order_mul
  have hfactor :
      (f - g) * q = f ^ n - g ^ n := by
    exact (Commute.all f g).mul_geom_sum₂ n
  calc
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
        (f - g).order + q.order :=
      add_le_add_right hq _
    _ ≤ ((f - g) * q).order :=
      MvPowerSeries.le_order_mul
    _ = (f ^ n - g ^ n).order :=
      congrArg (fun h : MvPowerSeries τ R => h.order) hfactor

private theorem order_prod_pow_sub_for_d017
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) :
    (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
      ((∏ i ∈ s, (f i) ^ n i) -
        ∏ i ∈ s, (g i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, sub_self, MvPowerSeries.order_zero]
      exact le_top
  | @insert i s hi ih =>
      have hni : n i ≠ 0 :=
        hn i (Finset.mem_insert_self i s)
      have hpowDifference :
          ((n i + 1 : ℕ) : ℕ∞) ≤
            ((f i) ^ n i - (g i) ^ n i).order := by
        calc
          ((n i + 1 : ℕ) : ℕ∞) =
              (2 : ℕ∞) + ((n i - 1 : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ (f i - g i).order +
              ((n i - 1 : ℕ) : ℕ∞) :=
            add_le_add_left
              (hfg i (Finset.mem_insert_self i s)) _
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order :=
            order_pow_sub_for_d017
              (f i) (g i)
              (hf i (Finset.mem_insert_self i s))
              (hg i (Finset.mem_insert_self i s))
              (n i)
      have hprodF :
          ((∑ j ∈ s, n j : ℕ) : ℕ∞) ≤
            (∏ j ∈ s, (f j) ^ n j).order :=
        order_prod_pow_for_d017 f n
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hpowG :
          (n i : ℕ∞) ≤ ((g i) ^ n i).order :=
        order_pow_for_d017
          (g i) (n i) (hg i (Finset.mem_insert_self i s))
      have hprodDifference :
          (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((∏ j ∈ s, (f j) ^ n j) -
              ∏ j ∈ s, (g j) ^ n j).order :=
        ih
          (fun j hj => hn j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
      have hleft :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              ((n i + 1 : ℕ) : ℕ∞) +
                ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order +
              (∏ j ∈ s, (f j) ^ n j).order :=
            add_le_add hpowDifference hprodF
          _ ≤ (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order :=
            MvPowerSeries.le_order_mul
      have hright :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              (n i : ℕ∞) +
                (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) := by
            norm_cast
          _ ≤ ((g i) ^ n i).order +
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j).order :=
            add_le_add hpowG hprodDifference
          _ ≤ ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order :=
            MvPowerSeries.le_order_mul
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi]
      rw [show
        (f i) ^ n i * (∏ j ∈ s, (f j) ^ n j) -
            (g i) ^ n i * (∏ j ∈ s, (g j) ^ n j) =
          ((f i) ^ n i - (g i) ^ n i) *
              (∏ j ∈ s, (f j) ^ n j) +
            (g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j) by ring]
      exact
        (le_min hleft hright).trans
          MvPowerSeries.min_order_le_add

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

private theorem constantCoeff_linear_for_d017
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff
        (d011 π i) = 0 := by
  rw [d011, map_mul,
    MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

private theorem hasSubst_linear_for_d017 [Finite σ]
    (π : F.valuationSubring) :
    MvPowerSeries.HasSubst
      (d011 (σ := σ) π) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (constantCoeff_linear_for_d017 π)

private theorem one_le_order_inVariable_for_d017
    (ebar : LubinTateSeries F π) (i : σ) :
    (1 : ℕ∞) ≤ (inVariable ebar i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)

private theorem one_le_order_linear_for_d017
    (π : F.valuationSubring) (i : σ) :
    (1 : ℕ∞) ≤ (d011 π i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_linear_for_d017 π i)

private theorem two_le_order_sub_linear_for_d017
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤
      (inVariable ebar i -
        d011 π i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero, Finsupp.single_zero]
      subst d
      simp [inVariable, d011,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        have hdegree : d.degree = d i := by
          simpa only [Finsupp.degree_single] using
            congrArg Finsupp.degree hdi
        have hlt : d i < 2 := by
          rw [← hdegree]
          exact hd
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, d011,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h, Finsupp.single_eq_same]
    have hX :
        MvPowerSeries.coeff d
          (MvPowerSeries.X i :
            MvPowerSeries σ F.valuationSubring) = 0 := by
      rw [MvPowerSeries.coeff_X, ite_eq_right hsingle]
    simp [inVariable, d011,
      PowerSeries.coeff_subst_single, hdi, hX]

/-- NYLL M351.017: substituting a monomial into the Lubin--Tate series and
into its linear model gives a difference of order at least its degree plus one. -/
theorem d017 [Finite σ]
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    d017Statement ebar d c := by
  unfold d017Statement
  have hprod :
      ((d.degree + 1 : ℕ) : ℕ∞) ≤
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n =>
            (d011 π i) ^ n)).order := by
    simpa only [Finsupp.prod, Finsupp.degree_apply] using
      order_prod_pow_sub_for_d017
        (s := d.support)
        (fun i : σ => inVariable ebar i)
        (d011 (σ := σ) π)
        (fun i => d i)
        (fun i hi => Finsupp.mem_support_iff.mp hi)
        (fun i _ => one_le_order_inVariable_for_d017 ebar i)
        (fun i _ =>
          one_le_order_linear_for_d017 π i)
        (fun i _ =>
          two_le_order_sub_linear_for_d017
            ebar i)
  rw [
    MvPowerSeries.subst_monomial
      (inVariable_hasSubst ebar) d c,
    MvPowerSeries.subst_monomial
      (hasSubst_linear_for_d017 (σ := σ) π) d c,
    ← MvPowerSeries.c_eq_algebraMap]
  rw [show
    MvPowerSeries.C c *
          d.prod (fun i n => (inVariable ebar i) ^ n) -
        MvPowerSeries.C c *
          d.prod (fun i n =>
            (d011 π i) ^ n) =
      c •
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n =>
            (d011 π i) ^ n)) by
    rw [MvPowerSeries.smul_eq_C_mul]
    ring]
  exact hprod.trans MvPowerSeries.le_order_smul

end Langlands.NYLL.PortInternal.M351

end
