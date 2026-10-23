import Langlands.Algebra.CommutingDimensionRecurrence

/-! Nilpotent case of the commuting-algebra dimension estimate. -/

noncomputable section
open scoped Pointwise IsMulCommutative

namespace Langlands.CommutingDimension

universe uK uV

variable (K : Type uK) [Field K]

set_option maxHeartbeats 800000 in
/-- The real dimension estimate for a family of commuting nilpotent endomorphisms. -/
theorem nilpotent_dimension (l : ℕ) :
    ∀ (V : Type uV) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (a : Fin l → Module.End K V),
      (∀ i j, Commute (a i) (a j)) →
      (∀ i, IsNilpotent (a i)) →
      (Module.finrank K (Algebra.adjoin K (Set.range a)) : ℝ) ≤
        (Module.finrank K V : ℝ) ^ dimensionExponent l := by
  induction l with
  | zero =>
    intro V _ _ _ a _ _
    simpa only [dimensionExponent_zero, Real.rpow_zero, Nat.cast_le_one] using
      zero_generators K V a
  | succ l ih =>
    suffices hall : ∀ m, ∀ (V : Type uV) [AddCommGroup V] [Module K V]
        [FiniteDimensional K V], Module.finrank K V = m →
        ∀ (a : Fin (l + 1) → Module.End K V),
        (∀ i j, Commute (a i) (a j)) →
        (∀ i, IsNilpotent (a i)) →
        (Module.finrank K (Algebra.adjoin K (Set.range a)) : ℝ) ≤
          (Module.finrank K V : ℝ) ^ dimensionExponent (l + 1) by
      intro V _ _ _ a hc hn
      exact hall (Module.finrank K V) V rfl a hc hn
    intro m
    induction m using Nat.strong_induction_on with
    | h m ihm =>
      intro V _ _ _ hm a hc hn
      rcases subsingleton_or_nontrivial V with hV | hV
      · let := hV
        rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      let := hV
      let C := Algebra.adjoin K (Set.range a)
      let : IsMulCommutative C := Algebra.isMulCommutative_adjoin K (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
        exact hc i j)
      let b : Fin (l + 1) → C := fun i =>
        ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
      have hb : Algebra.adjoin K (Set.range b) = ⊤ := adjoin_generators_top K a
      have hbn : ∀ i, IsNilpotent (b i) := by
        intro i
        exact (IsNilpotent.map_iff (f := C.val) Subtype.val_injective).mp (hn i)
      let J : Ideal C := Ideal.span (Set.range b)
      have hJ : J ≤ (⊥ : Ideal C).radical := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        obtain ⟨n, hn⟩ := hbn i
        exact ⟨n, hn⟩
      let W := (J • (⊤ : Submodule C V)).restrictScalars K
      have hW : ∀ c : C, ∀ v ∈ W, c.val v ∈ W := by
        intro c v hv
        exact (J • (⊤ : Submodule C V)).smul_mem c hv
      have hbW : ∀ i, ∀ v : V, (b i).val v ∈ W := by
        intro i v
        change b i • v ∈ J • (⊤ : Submodule C V)
        have hj : b i ∈ J := Ideal.subset_span (Set.mem_range_self i)
        exact Submodule.smul_mem_smul hj (Submodule.mem_top : v ∈ (⊤ : Submodule C V))
      let f := restrictionAlgHom K V C W hW
      let aW : Fin (l + 1) → Module.End K W := fun i => f (b i)
      have haW : Algebra.adjoin K (Set.range aW) = f.range :=
        adjoin_image_generators K b hb f
      have hWdim : Module.finrank K W < Module.finrank K V :=
        Submodule.finrank_lt (radical_action_ne_top K V C J hJ)
      have hsmall := ihm (Module.finrank K W) (by omega) W rfl aW
        (fun i j => (Commute.all (b i) (b j)).map f)
        (fun i => (hbn i).map f)
      rw [haW] at hsmall
      have htail := ih V (Fin.tail a)
        (fun i j => hc i.succ j.succ) (fun i => hn i.succ)
      have htaildim :
          Module.finrank K (Algebra.adjoin K (Set.range (Fin.tail b))) =
            Module.finrank K (Algebra.adjoin K (Set.range (Fin.tail a))) :=
        finrank_adjoin_map K (Fin.tail b) C.val Subtype.val_injective
      have hsplit := dimension_recurrence K V C b hb W hW (hbW 0)
      rw [htaildim] at hsplit
      have hgenerate := dimension_le_radical_codimension K V C J hJ
      have hdimle : Module.finrank K W ≤ Module.finrank K V := hWdim.le
      apply real_dimension_step (Module.finrank K V)
        (Module.finrank K V - Module.finrank K W) _
        (dimensionExponent (l + 1))
      · exact_mod_cast (Module.finrank_pos (R := K) (M := V))
      · exact sub_nonneg.mpr (by exact_mod_cast hdimle)
      · exact sub_le_self _ (Nat.cast_nonneg _)
      · exact dimensionExponent_succ_ge_one l
      · have hg : (Module.finrank K C : ℝ) ≤
            ((Module.finrank K V - Module.finrank K W : ℕ) : ℝ) *
              (Module.finrank K V : ℝ) := by exact_mod_cast hgenerate
        rwa [Nat.cast_sub hdimle] at hg
      · have hs : (Module.finrank K C : ℝ) ≤
            (Module.finrank K (Algebra.adjoin K (Set.range (Fin.tail a))) : ℝ) +
              (Module.finrank K f.range : ℝ) := by exact_mod_cast hsplit
        have he := dimensionExponent_recurrence l
        rw [he] at htail
        have hsub : (Module.finrank K V : ℝ) -
            ((Module.finrank K V : ℝ) - Module.finrank K W) =
              (Module.finrank K W : ℝ) := by ring
        rw [hsub]
        linarith

end Langlands.CommutingDimension
