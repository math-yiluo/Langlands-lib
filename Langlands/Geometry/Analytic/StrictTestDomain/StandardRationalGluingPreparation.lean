import Langlands.Geometry.Analytic.StrictTestDomain.RationalRelativeComparison
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover
import Mathlib.Topology.Order.Lattice

/-! # Uniform scalar thresholds and degenerate cases for rational descent -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- An empty point-cover of the whole spectrum forces the base to be zero. -/
theorem subsingleton_of_empty_whole_cover {I : Type v} [IsEmpty I]
    (D : I → RationalData K P)
    (hc : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) : Subsingleton P := by
  by_contra h
  have : Nontrivial P := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨x⟩ := PresentedStrictAffinoidAlgebra.spectrum_nonempty P
  obtain ⟨i, _⟩ := hc x
  exact isEmptyElim i

/-- The actual unique-section conclusion for an empty whole-spectrum cover. -/
theorem existsUnique_whole_gluing_empty {I : Type v} [IsEmpty I]
    (D : I → RationalData K P)
    (hc : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra) : ∃! a : P, ∀ i, (D i).baseMap a = s i := by
  let := subsingleton_of_empty_whole_cover D hc
  exact ⟨0, fun i => isEmptyElim i, fun _ _ => Subsingleton.elim _ _⟩

/-- The denominators of a point-cover generate the unit ideal. No finiteness
or assumption on the scalar valuation is needed for this elementary fact. -/
theorem span_denominators_eq_top_of_whole_cover {I : Type v}
    (D : I → RationalData K P)
    (hc : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) :
    Ideal.span (Set.range (fun i => (D i).denominator)) = ⊤ := by
  by_contra h
  obtain ⟨x, hx⟩ := PresentedStrictAffinoidAlgebra.exists_spectrum_kernel_of_proper_ideal
    P (Ideal.span (Set.range (fun i => (D i).denominator))) h
  obtain ⟨i, hi⟩ := hc x
  exact RationalFactorization.denominator_ne_zero K P (D i).arity (D i).denominator
    (D i).numerator (D i).generatesUnitIdeal x hi
      (hx (Ideal.subset_span (Set.mem_range_self i)))

omit [CompleteSpace K] in
/-- A finite tuple without common spectrum zero has a uniform positive
threshold below at least one entry at every point. -/
theorem exists_positive_uniform_threshold {n : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : BanachSpectrum P, ∃ j, ε < x (f j) := by
  classical
  by_cases hn : Nonempty (Fin n)
  · let := hn
    let F : BanachSpectrum P → ℝ := fun x =>
      Finset.univ.sup' Finset.univ_nonempty (fun j => x (f j))
    have hF : Continuous F := Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun j _ => (BanachSpectrum.evaluation (f j)).continuous)
    have hpos : ∀ x : BanachSpectrum P, 0 < F x := by
      intro x
      obtain ⟨j, hj⟩ := hf x
      exact (lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm (f j)) (Ne.symm hj)).trans_le
        (Finset.le_sup' (fun k => x (f k)) (Finset.mem_univ j))
    obtain ⟨ε, hε, he⟩ := isCompact_univ.exists_forall_le' hF.continuousOn
      (fun x _ => hpos x)
    refine ⟨ε / 2, half_pos hε, fun x => ?_⟩
    have hx : ε / 2 < F x := (half_lt_self hε).trans_le (he x (Set.mem_univ x))
    change ε / 2 < Finset.univ.sup' Finset.univ_nonempty (fun j => x (f j)) at hx
    obtain ⟨j, _, hj⟩ := (Finset.lt_sup'_iff Finset.univ_nonempty).mp hx
    exact ⟨j, hj⟩
  · refine ⟨1, zero_lt_one, fun x => ?_⟩
    obtain ⟨j, _⟩ := hf x
    exact (hn ⟨j⟩).elim

omit [CompleteSpace K] in
/-- In the nontrivial-valuation branch the positive real threshold can be
replaced by the norm of a nonzero scalar. -/
theorem exists_scalar_uniform_threshold (hK : ∃ c : K, 1 < ‖c‖)
    {n : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f j) := by
  let _ : NontriviallyNormedField K :=
    { toNormedField := inferInstance, non_trivial := hK }
  obtain ⟨ε, hε, he⟩ := exists_positive_uniform_threshold f hf
  obtain ⟨c, hc, hce⟩ := NormedField.exists_norm_lt K hε
  refine ⟨c, norm_pos_iff.mp hc, fun x => ?_⟩
  obtain ⟨j, hj⟩ := he x
  exact ⟨j, hce.trans hj⟩

/-- Every actual quotient over a zero base is zero, so any family has a unique
scalar lift in this case. -/
theorem existsUnique_whole_gluing_of_subsingleton [Subsingleton P] {I : Type v}
    (D : I → RationalData K P) (s : ∀ i, (D i).algebra) :
    ∃! a : P, ∀ i, (D i).baseMap a = s i := by
  have hz (i : I) : (0 : (D i).algebra) = 1 := by
    have h := congrArg (D i).baseMap.toAlgHom (Subsingleton.elim (0 : P) 1)
    simpa only [map_zero, map_one] using h
  have hs (i : I) : Subsingleton (D i).algebra := subsingleton_of_zero_eq_one (hz i)
  exact ⟨0, fun i => (hs i).elim _ _, fun _ _ => Subsingleton.elim _ _⟩

omit [CompleteSpace K] in
/-- A chosen nonzero scalar whose norm is strictly below some tuple entry at
 every spectrum point. This packages the proved uniform-threshold existence. -/
def scalarUniformThreshold (hK : ∃ c : K, 1 < ‖c‖)
    {n : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0) :
    {c : K // c ≠ 0 ∧ ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f j)} :=
  ⟨Classical.choose (exists_scalar_uniform_threshold hK f hf),
    Classical.choose_spec (exists_scalar_uniform_threshold hK f hf)⟩

/-- The empty standard tuple has the actual unique-section conclusion. -/
theorem existsUnique_standard_gluing_empty (f : Fin 0 → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0)
    (s : ∀ j : Fin 0, (standardRational f hf j).algebra) :
    ∃! a : P, ∀ j, (standardRational f hf j).baseMap a = s j := by
  exact existsUnique_whole_gluing_empty (standardRational f hf)
    (standardRational_covers f hf) s

end Langlands.Analytic.StrictTestDomain
