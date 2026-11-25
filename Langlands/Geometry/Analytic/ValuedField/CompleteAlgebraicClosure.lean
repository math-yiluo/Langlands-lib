/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang

The dense algebraic-closedness proof below is adapted from Mathlib's
Analysis/Normed/Field/Dense.lean, replacing its characteristic-zero input
by the perfectness lemma proved here.
-/
import Mathlib.Analysis.Normed.Field.Dense
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.FieldTheory.Perfect
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Langlands.Geometry.Analytic.Spectrum.NonarchimedeanDominationProof
import Langlands.Geometry.Analytic.Spectrum.Properties
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraic closedness and complete normed extensions in all characteristics -/

noncomputable section

namespace Langlands.Analytic.ValuedField

open Polynomial

/-- A complete normed field with a dense perfect subfield is perfect. -/
theorem perfectField_of_denseRange {K L : Type*} [Field K] [NormedField L]
    [CompleteSpace L] [Algebra K L] [PerfectField K]
    (hi : DenseRange (algebraMap K L)) : PerfectField L := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  let : ExpChar K p := hp
  let : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  have hdist (a b : L) : dist (frobenius L p a) (frobenius L p b) = dist a b ^ p := by
    rw [dist_eq_norm, ← map_sub, frobenius_def, norm_pow, dist_eq_norm]
  have hu : IsUniformInducing (frobenius L p) := by
    refine Metric.isUniformInducing_iff.mpr ⟨?_, ?_⟩
    · exact uniformContinuous_addMonoidHom_of_continuous (f := (frobenius L p).toAddMonoidHom)
        (continuous_pow p)
    · intro ε hε
      refine ⟨ε ^ p, pow_pos hε p, ?_⟩
      intro a b hab
      rw [hdist] at hab
      exact lt_of_pow_lt_pow_left₀ p hε.le hab
  let : PerfectRing L p := PerfectRing.ofSurjective L p (by
    have hs : Set.range (algebraMap K L) ⊆ Set.range (frobenius L p) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := surjective_frobenius K p x
      refine ⟨algebraMap K L y, ?_⟩
      simpa only [frobenius_def, map_pow] using congrArg (algebraMap K L) hy
    have hd : DenseRange (frobenius L p) := hi.mono hs
    intro y
    have hy : y ∈ closure (Set.range (frobenius L p)) := hd y
    rw [hu.isComplete_range.isClosed.closure_eq] at hy
    exact hy)
  exact PerfectRing.toPerfectField L p

/-- The completion step for a dense algebraically closed subfield does not
require characteristic zero. -/
theorem isAlgClosed_of_denseRange_nontrivial {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L := by
  let : PerfectField L := perfectField_of_denseRange hi
  -- Fix any monic irreducible polynomial `f` in `L`.
  -- Let `F` be the splitting field of `f`. Let `a` be a root of `f` in `F`.
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  let : NormedField F := spectralNorm.normedField L F
  let : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  -- Let `δ` be a positive real number such that `δ ≤ ‖a - a'‖` for
  -- every Galois conjugates `a'` of `a`
  classical
    let S : Finset F := {x ∈ (f.rootSet F).toFinset | x ≠ a}
  let δ : ℝ := if hS : S.Nonempty then Finset.min' (S.image fun x => ‖a - x‖)
      (Finset.image_nonempty.mpr hS) else 1
  have norm_sub_le : ∀ a' : F, IsConjRoot L a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · apply Finset.min'_le (S.image fun x => ‖a - x‖) (‖a - a'‖)
      apply Finset.mem_image_of_mem
      simp only [minpoly.eq_of_irreducible_of_monic firr fa0 fmon, Finset.mem_filter,
        Set.mem_toFinset, S]
      rw [← (isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩)]
      exact ⟨conj, ne.symm⟩
    · simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
      Set.mem_toFinset, not_not, S] at hS
      rw [isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩,
          ← minpoly.eq_of_irreducible_of_monic firr fa0 fmon] at conj
      exact (ne (hS conj).symm).elim
  have δpos : δ > 0 := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [gt_iff_lt, Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro a' ha'
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at ha'
      rw [norm_pos_iff, sub_ne_zero]
      exact ha'.2.symm
    · linarith
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  -- We can find a `g ∈ K[X]` whose coefficients sufficiently close to coefficients of `f`.
  -- By continuity of roots, there exists a root `b` of `g` in `K` such that `‖a - b‖ ≤ δ`.
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  let ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
      (by simpa [Polynomial.map_map] using (IsAlgClosed.splits g).map ((algebraMap L F).comp _))
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have bbot : b ∈ (⊥ : IntermediateField L F) := by
    rw [Polynomial.aroots_def, Splits.roots_map ((IsAlgClosed.splits g).map _),
        Multiset.mem_map] at hb
    obtain ⟨bCp, _, hbCp⟩ := hb
    rw [IntermediateField.mem_bot]
    exact ⟨bCp, hbCp⟩
  simp only [Polynomial.mem_roots', ne_eq, Polynomial.map_eq_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map_algebraMap] at hb
  -- By Krasner's lemma, `a ∈ L(b) = L`. Thus `f` has a root in `L`.
  have abot : a ∈ (⊥ : IntermediateField L F) := by
    have masp : ((minpoly L a).map (algebraMap L F)).Splits := by
      simpa [minpoly.eq_of_irreducible_of_monic firr fa0 fmon] using
        (Polynomial.SplittingField.splits f)
    simpa [IntermediateField.adjoin_simple_eq_bot_iff.mpr bbot] using
      IsKrasner.krasner (PerfectField.separable_of_irreducible (minpoly.irreducible ⟨f, fmon, fa0⟩))
        masp ⟨(g.map _), gmon.map _, hb.2⟩ fun a' h1 h2 ↦ lt_of_lt_of_le hab (norm_sub_le a' h1 h2)
  obtain ⟨aCp, haCp⟩ := IntermediateField.mem_bot.mp abot
  use aCp
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, haCp, map_zero]
  · exact RingHom.injective _

/-- A complete ultrametric field with a dense algebraically closed subfield
is algebraically closed, including for a trivial norm. -/
theorem isAlgClosed_of_denseRange {K L : Type*} [Field K] [NormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField L with h | ⟨h, heq⟩
  · let : DiscreteTopology L := h
    let e := RingEquiv.ofBijective (algebraMap K L)
      ⟨(algebraMap K L).injective, denseRange_discrete.mp hi⟩
    apply IsAlgClosed.of_exists_root
    intro p hmp hp
    have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
      rw [degree_map]
      exact ne_of_gt (degree_pos_of_irreducible hp)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map e.symm.toRingHom) hpe
    use e x
    rw [IsRoot] at hx
    apply e.symm.injective
    rw [map_zero, ← hx]
    clear hx hpe hp hmp
    induction p using Polynomial.induction_on <;> simp_all
  · cases heq
    exact isAlgClosed_of_denseRange_nontrivial hi

universe u

/-- Every ultrametric normed field has a complete algebraically closed
ultrametric normed extension in the same universe. -/
theorem exists_completeAlgebraicallyClosed_extension
    (K : Type u) [NormedField K] [IsUltrametricDist K] :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : IsAlgClosed L) (_ : NormedAlgebra K L), True := by
  let E := AlgebraicClosure K
  let p : RingSeminorm E := (spectralAlgNorm K E).toRingSeminorm
  obtain ⟨q, hq, hqp⟩ := BanachSpectrum.nonarchimedeanDomination E p
    spectralAlgNorm_one isNonarchimedean_spectralNorm
  let abv : AbsoluteValue E ℝ := {
    toFun := q
    map_mul' := map_mul q
    nonneg' := apply_nonneg q
    eq_zero' := fun x => by
      constructor
      · intro hx
        by_contra hne
        have h := map_mul q x x⁻¹
        rw [mul_inv_cancel₀ hne, map_one, hx, zero_mul] at h
        exact one_ne_zero h
      · rintro rfl
        exact map_zero q
    add_le' := map_add_le_add q
  }
  let : NormedField E := abv.toNormedField
  let : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hq
  have hK (a : K) : ‖algebraMap K E a‖ = ‖a‖ := by
    let x : BanachSpectrum K := {
      toFun := fun a => ‖algebraMap K E a‖
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul, norm_mul]
      add_le' := fun a b => by rw [map_add]; exact norm_add_le _ _
      neg' := fun a => by rw [map_neg, norm_neg]
      le_norm := fun a => (hqp (algebraMap K E a)).trans_eq (spectralAlgNorm_extends a)
    }
    exact BanachSpectrum.field_apply x a
  let : NormedAlgebra K E := {
    norm_smul_le a b := by rw [Algebra.smul_def, norm_mul, hK]
  }
  let L := UniformSpace.Completion E
  let : IsUltrametricDist L := by
    apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    intro a b
    induction a, b using UniformSpace.Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a b =>
      change ‖(a : UniformSpace.Completion E) + (b : UniformSpace.Completion E)‖ ≤
        max ‖(a : UniformSpace.Completion E)‖ ‖(b : UniformSpace.Completion E)‖
      rw [← UniformSpace.Completion.coe_add]
      simpa only [UniformSpace.Completion.norm_coe] using
        IsUltrametricDist.norm_add_le_max a b
  let : IsAlgClosed L := isAlgClosed_of_denseRange
    (show DenseRange (algebraMap E L) from UniformSpace.Completion.denseRange_coe)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩

/-- A chosen complete algebraically closed ultrametric extension of `K`.
Its norm and algebra structure are chosen together below. -/
def CompleteAlgebraicClosure (K : Type u) [NormedField K] [IsUltrametricDist K] : Type u :=
  (exists_completeAlgebraicallyClosed_extension K).choose

namespace CompleteAlgebraicClosure

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

instance instNormedField : NormedField (CompleteAlgebraicClosure K) :=
  (exists_completeAlgebraicallyClosed_extension K).choose_spec.choose

instance instIsUltrametricDist : IsUltrametricDist (CompleteAlgebraicClosure K) :=
  (exists_completeAlgebraicallyClosed_extension K).choose_spec.choose_spec.choose

instance instCompleteSpace : CompleteSpace (CompleteAlgebraicClosure K) :=
  (exists_completeAlgebraicallyClosed_extension K).choose_spec.choose_spec.choose_spec.choose

instance instIsAlgClosed : IsAlgClosed (CompleteAlgebraicClosure K) :=
  (exists_completeAlgebraicallyClosed_extension K).choose_spec.choose_spec.choose_spec.choose_spec.choose

instance instNormedAlgebra : NormedAlgebra K (CompleteAlgebraicClosure K) :=
  (exists_completeAlgebraicallyClosed_extension K).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The structural embedding preserves the given norm exactly. -/
theorem norm_algebraMap (a : K) : ‖algebraMap K (CompleteAlgebraicClosure K) a‖ = ‖a‖ :=
  norm_algebraMap' _ _

end CompleteAlgebraicClosure

end Langlands.Analytic.ValuedField
