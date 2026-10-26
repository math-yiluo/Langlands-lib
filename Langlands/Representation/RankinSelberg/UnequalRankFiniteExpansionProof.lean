import Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionStatement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.HarmonicAnalysis.CompactCosetExpansion

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Topology

universe uF uV

section Rectangular

variable {F : Type uF} [Field F] {n : ℕ} (j k : ℕ)

/-- Any two rectangular off-diagonal blocks have zero product. -/
theorem rectangularEntries_mul (x y : Matrix (Fin j) (Fin (n + 1)) F) :
    rectangularEntries j k x * rectangularEntries j k y = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c.val < n + 1
  · have hr : ¬ (n + 1 ≤ c.val ∧ c.val < n + 1 + j) := by omega
    simp only [rectangularEntries, dite_eq_right hr, mul_zero]
  · simp [rectangularEntries, hc]

theorem rectangularEntries_add (x y : Matrix (Fin j) (Fin (n + 1)) F) :
    rectangularEntries j k (x + y) = rectangularEntries j k x + rectangularEntries j k y := by
  ext a b
  simp only [rectangularEntries, Matrix.add_apply]
  split_ifs <;> simp

@[simp] theorem rectangularUnipotent_zero :
    rectangularUnipotent (n := n) (F := F) j k 0 = 1 := by
  apply Units.ext
  ext a b
  simp [rectangularUnipotent, rectangularEntries]

theorem rectangularUnipotent_add (x y : Matrix (Fin j) (Fin (n + 1)) F) :
    rectangularUnipotent j k (x + y) =
      rectangularUnipotent j k x * rectangularUnipotent j k y := by
  apply Units.ext
  change 1 + rectangularEntries j k (x + y) =
    (1 + rectangularEntries j k x) * (1 + rectangularEntries j k y)
  simp only [rectangularEntries_add, add_mul, mul_add, one_mul, mul_one,
    rectangularEntries_mul, add_zero]
  abel

@[simp] theorem rectangularUnipotent_neg (x : Matrix (Fin j) (Fin (n + 1)) F) :
    rectangularUnipotent j k (-x) = (rectangularUnipotent j k x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rectangularUnipotent_add, neg_add_cancel, rectangularUnipotent_zero]

variable [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
theorem continuous_rectangularEntries :
    Continuous (rectangularEntries (n := n) (F := F) j k) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rectangularEntries]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const

/-- Continuity uses both the matrix and its explicit inverse. -/
theorem continuous_rectangularUnipotent :
    Continuous (rectangularUnipotent (n := n) (F := F) j k) := by
  apply Units.continuous_iff.mpr
  exact ⟨continuous_const.add (continuous_rectangularEntries j k),
    continuous_const.sub (continuous_rectangularEntries j k)⟩

end Rectangular

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Intersecting a pulled-back open subgroup with integral matrices makes it compact. -/
theorem exists_compactOpen_rectangular_subgroup (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ K : OpenSubgroup (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier),
      ∃ U : OpenAddSubgroup (Matrix (Fin j) (Fin (n + 1)) F.Carrier),
        IsCompact (U : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier)) ∧ ∀ x ∈ U, rectangularUnipotent j k x ∈ K := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro K
  let L : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier) :=
    Set.univ.pi (fun _ => Set.univ.pi (fun _ => (T.Integers : Set F.Carrier)))
  have hL (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier) :
      x ∈ L ↔ ∀ a b, x a b ∈ T.Integers := by
    change (∀ a, a ∈ Set.univ → ∀ b, b ∈ Set.univ → x a b ∈ T.Integers) ↔ _
    simp
  have hLc : IsCompact L :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => T.isCompact_integers))
  have hLo : IsOpen L :=
    isOpen_set_pi Set.finite_univ (fun _ _ =>
      isOpen_set_pi Set.finite_univ (fun _ _ => T.isOpen_integers))
  let U : OpenAddSubgroup (Matrix (Fin j) (Fin (n + 1)) F.Carrier) :=
    { carrier := {x | rectangularUnipotent j k x ∈ K} ∩ L
      zero_mem' := ⟨by simp, (hL 0).mpr (fun _ _ => T.Integers.zero_mem)⟩
      add_mem' := by
        intro x y hx hy
        refine ⟨?_, (hL (x + y)).mpr ?_⟩
        · change rectangularUnipotent j k (x + y) ∈ K
          rw [rectangularUnipotent_add]
          exact K.mul_mem hx.1 hy.1
        · intro a b
          exact T.Integers.add_mem ((hL x).mp hx.2 a b) ((hL y).mp hy.2 a b)
      neg_mem' := by
        intro x hx
        refine ⟨?_, (hL (-x)).mpr ?_⟩
        · change rectangularUnipotent j k (-x) ∈ K
          rw [rectangularUnipotent_neg]
          exact K.inv_mem hx.1
        · intro a b
          exact T.Integers.neg_mem ((hL x).mp hx.2 a b)
      isOpen' := (K.isOpen.preimage (continuous_rectangularUnipotent j k)).inter hLo }
  exact ⟨U, hLc.of_isClosed_subset U.isClosed (fun _ hx => hx.2), fun _ hx => hx.1⟩

/-- Smoothness supplies one compact open translation subgroup for all block arguments. -/
theorem unequalRank_coefficient_invariant (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V),
      IsSmooth π → ∀ (ℓ : glFunctionals ψ (n + (j + k + 1)) π)
      (f : (coefficientModel π ℓ).toSubmodule),
      ∃ U : OpenAddSubgroup (Matrix (Fin j) (Fin (n + 1)) F.Carrier),
        IsCompact (U : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier)) ∧
        ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) x a, a ∈ U →
          f.val.val (unequalRankMatrix j k g (x + a)) =
            f.val.val (unequalRankMatrix j k g x) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π hπ ℓ f
  obtain ⟨K, hK⟩ := model_isSmooth π hπ ℓ f
  obtain ⟨U, hUc, hUK⟩ := exists_compactOpen_rectangular_subgroup F T n j k K
  refine ⟨U, hUc, ?_⟩
  intro g x a ha
  have heq := congrArg (fun w : (coefficientModel π ℓ).toSubmodule =>
    w.val.val (unequalRankMatrix j k g x)) (hK ⟨rectangularUnipotent j k a, hUK a ha⟩)
  change f.val.val (unequalRankMatrix j k g x * rectangularUnipotent j k a) =
    f.val.val (unequalRankMatrix j k g x) at heq
  simpa only [unequalRankMatrix, rectangularUnipotent_add, mul_assoc] using heq

/-- The representation-specific assembly, conditional on the generic coset expansion. -/
theorem unequalRankFiniteExpansion_of_cosetExpansion (n j k : ℕ)
    (hexpand :
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      ∀ (U : OpenAddSubgroup (Matrix (Fin j) (Fin (n + 1)) F.Carrier)),
        IsCompact (U : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier)) →
        ∀ H : Langlands.GeneralLinear (n + 1) F.Carrier →
          Matrix (Fin j) (Fin (n + 1)) F.Carrier → ℂ,
          (∀ g x a, a ∈ U → H g (x + a) = H g x) →
          (∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier),
            IsCompact C ∧ ∀ g x, H g x ≠ 0 → x ∈ C) →
          ∃ (m : ℕ)
            (φ : Fin m → SchwartzBruhat (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
            (r : Fin m → Matrix (Fin j) (Fin (n + 1)) F.Carrier),
            ∀ g x, H g x = ∑ i : Fin m, φ i x * H g (r i)) :
    UnequalRankFiniteExpansionStatement.{uF,uV} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π hπ ℓ _ f hC
  obtain ⟨U, hUc, hU⟩ := unequalRank_coefficient_invariant F T n j k ψ V π hπ.1.1 ℓ f
  obtain ⟨m, φ, r, hr⟩ := hexpand U hUc
    (fun g x => f.val.val (unequalRankMatrix j k g x)) hU hC
  refine ⟨m, φ, fun i => modelRepresentation π ℓ (rectangularUnipotent j k (r i)) f, ?_⟩
  intro g x
  exact hr g x

/-- Uniform compact support gives a finite pointwise Schwartz expansion in the
original coefficient model, for all rectangular dimensions. -/
theorem unequalRankFiniteExpansion (n j k : ℕ) :
    UnequalRankFiniteExpansionStatement.{uF,uV} F T n j k := by
  apply unequalRankFiniteExpansion_of_cosetExpansion F T n j k
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  exact fun U hU H hinv hsupp => exists_compactCosetExpansion U hU H hinv hsupp

end Padic

end Langlands.RankinSelberg
