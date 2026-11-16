/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of M354.004
(HasLinearTerm.subst, source lines 88-167 of StandardFormalGroup.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709) as a proof of the
published target substStatement, under the namespace prefix Langlands.NYLL.
The draft reproved both source prerequisites as private lemmas.
Modified by Worker 331, 2026-11-16: reuse Worker 497's shared draft, import
the published M347.004 proof instead of its private duplicate, and retain
only the private weighted-sum lemma M354.003 under a non-conflicting name.
Bind the imported constant-coefficient law to its explicit equality because
its published statement is a def. Record every adaptation in the Markdown.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U004.Proofs

/-!
# M354.004: substitution composes linear terms

Proof of `HasLinearTerm.substStatement`: substituting series `G i` with
prescribed linear terms `M i` into a series `H` with prescribed linear term
`L` gives a series with linear term `fun j => ∑ i, L i * M i j`.
-/

open scoped BigOperators

universe w w'

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

namespace HasLinearTerm

/-- Local copy of M354.003: a weighted sum of linear forms is the linear
form of the weighted coefficients. -/
private theorem subst_weighted_sum_aux
    (L : σ → R) (M : σ → τ → R) :
    (∑ i, MvPowerSeries.C (L i) * linearForm (M i)) =
      linearForm (fun j => ∑ i, L i * M i j) := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [linearForm, map_sum, MvPowerSeries.coeff_C_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Substituting series with prescribed linear terms composes their linear
coefficient matrices (NYLL M354.004). -/
theorem subst
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    {G : σ → MvPowerSeries τ R} {M : σ → τ → R}
    (hG : ∀ i, HasLinearTerm (G i) (M i)) :
    substStatement hH hG := by
  have hGzero : ∀ i, MvPowerSeries.constantCoeff (G i) = 0 :=
    fun i => (hG i).constantCoeff_eq_zero
  have hGsubst : MvPowerSeries.HasSubst G :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      hGzero
  have hGorder : ∀ i, (1 : ℕ∞) ≤ (G i).order :=
    fun i =>
      MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
        (hGzero i)
  have hinf : (1 : ℕ∞) ≤ ⨅ i, (G i).order :=
    le_iInf hGorder
  have houter :
      (2 : ℕ∞) ≤
        (MvPowerSeries.subst G (H - linearForm L)).order := by
    refine
      (show
        (2 : ℕ∞) ≤
          (⨅ i, (G i).order) * (H - linearForm L).order by
        calc
          (2 : ℕ∞) = 1 * 2 := by norm_num
          _ ≤ (⨅ i, (G i).order) *
              (H - linearForm L).order :=
            mul_le_mul hinf hH bot_le bot_le).trans
        (MvPowerSeries.le_order_subst hGsubst
          (H - linearForm L))
  have hsubstLinear :
      MvPowerSeries.subst G (linearForm L) =
        ∑ i, MvPowerSeries.C (L i) * G i := by
    classical
    rw [linearForm,
      ← MvPowerSeries.substAlgHom_apply hGsubst, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, MvPowerSeries.substAlgHom_X,
      MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
  have hlinearIdentity :
      MvPowerSeries.subst G (linearForm L) -
          linearForm (fun j => ∑ i, L i * M i j) =
        ∑ i, MvPowerSeries.C (L i) *
          (G i - linearForm (M i)) := by
    rw [hsubstLinear, ← subst_weighted_sum_aux L M,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlinear :
      (2 : ℕ∞) ≤
        (MvPowerSeries.subst G (linearForm L) -
          linearForm (fun j => ∑ i, L i * M i j)).order := by
    rw [hlinearIdentity]
    apply MvPowerSeries.nat_le_order
    intro d hd
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [MvPowerSeries.coeff_C_mul]
    have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
      exact_mod_cast hd
    rw [MvPowerSeries.coeff_of_lt_order
      (hd'.trans_le (hG i)), mul_zero]
  rw [substStatement, HasLinearTerm]
  have hdecompose :
      MvPowerSeries.subst G H -
          linearForm (fun j => ∑ i, L i * M i j) =
        MvPowerSeries.subst G (H - linearForm L) +
          (MvPowerSeries.subst G (linearForm L) -
            linearForm (fun j => ∑ i, L i * M i j)) := by
    rw [MvPowerSeries.subst_sub hGsubst]
    ring
  rw [hdecompose]
  exact
    (le_min houter hlinear).trans
      MvPowerSeries.min_order_le_add

end HasLinearTerm

end SameUniformizer
end Langlands.NYLL.LubinTate
