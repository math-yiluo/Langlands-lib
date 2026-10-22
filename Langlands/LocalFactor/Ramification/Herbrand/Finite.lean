import Langlands.LocalFactor.Ramification.Herbrand.Real
import Langlands.LocalFactor.Ramification.Galois
import Langlands.LocalField.Canonical

/-!
# Herbrand functions of actual finite p-adic extensions

All groups are the published integer-ring ramification groups. The cutoff,
positivity, and inverse are constructed from their intrinsic properties.
-/

noncomputable section

namespace Langlands.Ramification.Padic

universe uK uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- Real lower numbering uses the smallest integer at least the argument.
The existing constant extension below `-1` is retained. -/
def lowerRamificationGroupReal (u : ℝ) : Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  lowerRamificationGroupInt T K ⌈u⌉

@[simp] theorem lowerRamificationGroupReal_int (i : ℤ) :
    lowerRamificationGroupReal T K i = lowerRamificationGroupInt T K i := by
  simp [lowerRamificationGroupReal]

@[simp] theorem lowerRamificationGroupReal_nat (i : ℕ) :
    lowerRamificationGroupReal T K i = lowerRamificationGroup T K i := by
  let := integerAction T K
  simp [lowerRamificationGroupReal, lowerRamificationGroupInt,
    lowerRamificationGroup, lowerGroupInt]

@[simp] theorem lowerRamificationGroupReal_neg_one :
    lowerRamificationGroupReal T K (-1) = ⊤ := by
  simpa only [Int.cast_neg, Int.cast_one] using
    (lowerRamificationGroupReal_int T K (-1)).trans
      (lowerRamificationGroupInt_neg_one T K)

@[simp] theorem lowerRamificationGroupReal_zero :
    lowerRamificationGroupReal T K 0 = inertia T K := by
  simpa using (lowerRamificationGroupReal_nat T K 0).trans
    (lowerRamificationGroup_zero T K)

instance lowerRamificationGroupInt_normal (i : ℤ) :
    (lowerRamificationGroupInt T K i).Normal := by
  let := integerAction T K
  unfold lowerRamificationGroupInt lowerGroupInt
  split <;> infer_instance

instance lowerRamificationGroupReal_normal (u : ℝ) :
    (lowerRamificationGroupReal T K u).Normal :=
  lowerRamificationGroupInt_normal T K _

theorem lowerRamificationGroupInt_antitone :
    Antitone (lowerRamificationGroupInt T K) := by
  let := integerAction T K
  intro i j hij
  unfold lowerRamificationGroupInt lowerGroupInt
  by_cases hi : i < 0
  · simp only [hi, ite_true]
    exact le_top
  · have hj : ¬ j < 0 := not_lt.mpr ((not_lt.mp hi).trans hij)
    simp only [hi, hj, ite_false]
    exact lowerGroup_antitone _ _ (Int.toNat_le_toNat hij)

theorem lowerRamificationGroupReal_antitone :
    Antitone (lowerRamificationGroupReal T K) := by
  intro u v huv
  exact lowerRamificationGroupInt_antitone T K (Int.ceil_mono huv)

/-- The actual order of the published lower group. -/
def lowerGroupOrder (i : ℕ) : ℕ := Nat.card (lowerRamificationGroup T K i)

theorem lowerGroupOrder_pos (i : ℕ) : 0 < lowerGroupOrder T K i := by
  let : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  exact Nat.card_pos

theorem lowerGroupOrder_one_le (i : ℕ) : 1 ≤ lowerGroupOrder T K i :=
  lowerGroupOrder_pos T K i

/-- An intrinsic cutoff chosen from the proved eventual triviality theorem. -/
def ramificationCutoff : ℕ := (exists_lowerRamificationGroup_eq_bot T K).choose

theorem lowerRamificationGroup_eq_bot_of_cutoff (i : ℕ)
    (hi : ramificationCutoff T K ≤ i) : lowerRamificationGroup T K i = ⊥ :=
  (exists_lowerRamificationGroup_eq_bot T K).choose_spec i hi

theorem lowerGroupOrder_tail (i : ℕ) (hi : ramificationCutoff T K ≤ i) :
    lowerGroupOrder T K (i + 1) = 1 := by
  unfold lowerGroupOrder
  rw [lowerRamificationGroup_eq_bot_of_cutoff T K (i + 1) (hi.trans (Nat.le_succ i))]
  simp

/-- Serre's real Herbrand function, extended by the identity below `-1`.
The positive branch is the floor formula, proved below. -/
def herbrandPhi (u : ℝ) : ℝ :=
  Herbrand.polygon (lowerGroupOrder T K) (ramificationCutoff T K) u

theorem herbrandPhi_floor {u : ℝ} (hu : 0 ≤ u) :
    herbrandPhi T K u =
      ((∑ i ∈ Finset.range ⌊u⌋₊, (lowerGroupOrder T K (i + 1) : ℝ)) +
        (u - ⌊u⌋₊) * lowerGroupOrder T K (⌊u⌋₊ + 1)) /
      lowerGroupOrder T K 0 :=
  Herbrand.polygon_floor _ _ (lowerGroupOrder_tail T K) hu

theorem herbrandPhi_of_nonpos {u : ℝ} (hu : u ≤ 0) : herbrandPhi T K u = u :=
  Herbrand.polygon_of_nonpos _ _ hu

@[simp] theorem herbrandPhi_zero : herbrandPhi T K 0 = 0 :=
  herbrandPhi_of_nonpos T K le_rfl

@[simp] theorem herbrandPhi_neg_one : herbrandPhi T K (-1) = -1 :=
  herbrandPhi_of_nonpos T K (by norm_num)

theorem herbrandPhi_continuous : Continuous (herbrandPhi T K) :=
  Herbrand.polygon_continuous _ _

theorem herbrandPhi_strictMono : StrictMono (herbrandPhi T K) :=
  Herbrand.polygon_strictMono (lowerGroupOrder_one_le T K)

theorem herbrandPhi_surjective : Function.Surjective (herbrandPhi T K) :=
  Herbrand.polygon_surjective (lowerGroupOrder_one_le T K)

/-- The constructed order isomorphism of the real indexing line. -/
def herbrandOrderIso : ℝ ≃o ℝ :=
  Herbrand.polygonOrderIso (lowerGroupOrder T K) (ramificationCutoff T K)
    (lowerGroupOrder_one_le T K)

/-- The genuine inverse Herbrand function. -/
def herbrandPsi (v : ℝ) : ℝ := (herbrandOrderIso T K).symm v

@[simp] theorem herbrandOrderIso_apply (u : ℝ) :
    herbrandOrderIso T K u = herbrandPhi T K u := rfl

@[simp] theorem herbrandPhi_herbrandPsi (v : ℝ) :
    herbrandPhi T K (herbrandPsi T K v) = v :=
  (herbrandOrderIso T K).apply_symm_apply v

@[simp] theorem herbrandPsi_herbrandPhi (u : ℝ) :
    herbrandPsi T K (herbrandPhi T K u) = u :=
  (herbrandOrderIso T K).symm_apply_apply u

theorem herbrandPsi_continuous : Continuous (herbrandPsi T K) :=
  (herbrandOrderIso T K).symm.continuous

theorem herbrandPsi_strictMono : StrictMono (herbrandPsi T K) :=
  (herbrandOrderIso T K).symm.strictMono

theorem herbrandPsi_of_nonpos {v : ℝ} (hv : v ≤ 0) : herbrandPsi T K v = v :=
  Herbrand.inverse_of_nonpos _ (ramificationCutoff T K) (lowerGroupOrder_one_le T K) hv

@[simp] theorem herbrandPsi_zero : herbrandPsi T K 0 = 0 :=
  herbrandPsi_of_nonpos T K le_rfl

@[simp] theorem herbrandPsi_neg_one : herbrandPsi T K (-1) = -1 :=
  herbrandPsi_of_nonpos T K (by norm_num)

/-- The same maps restricted to the original half-line `[-1,infinity)`. -/
def herbrandHalfLineOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) :=
  Herbrand.halfLineOrderIso _ (ramificationCutoff T K) (lowerGroupOrder_one_le T K)

theorem herbrandPhi_pos {u : ℝ} (hu : 0 < u) : 0 < herbrandPhi T K u := by
  simpa using herbrandPhi_strictMono T K hu

theorem herbrandPsi_pos {v : ℝ} (hv : 0 < v) : 0 < herbrandPsi T K v := by
  simpa using herbrandPsi_strictMono T K hv

/-- Actual upper numbering, obtained by reindexing the published lower groups
by the constructed inverse Herbrand function. -/
def upperRamificationGroup (v : ℝ) : Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  lowerRamificationGroupReal T K (herbrandPsi T K v)

theorem upperRamificationGroup_eq_lower (v : ℝ) :
    upperRamificationGroup T K v =
      lowerRamificationGroupInt T K ⌈herbrandPsi T K v⌉ := rfl

@[simp] theorem upperRamificationGroup_phi (u : ℝ) :
    upperRamificationGroup T K (herbrandPhi T K u) =
      lowerRamificationGroupReal T K u := by
  simp [upperRamificationGroup]

@[simp] theorem upperRamificationGroup_neg_one : upperRamificationGroup T K (-1) = ⊤ := by
  simp [upperRamificationGroup]

@[simp] theorem upperRamificationGroup_zero : upperRamificationGroup T K 0 = inertia T K := by
  simp [upperRamificationGroup]

instance upperRamificationGroup_normal (v : ℝ) :
    (upperRamificationGroup T K v).Normal :=
  lowerRamificationGroupReal_normal T K _

theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup T K) :=
  (lowerRamificationGroupReal_antitone T K).comp_monotone
    (herbrandPsi_strictMono T K).monotone

theorem lowerRamificationGroupReal_eq_bot_of_cutoff {u : ℝ}
    (hu : (ramificationCutoff T K : ℝ) ≤ u) :
    lowerRamificationGroupReal T K u = ⊥ := by
  let := integerAction T K
  have hc : (ramificationCutoff T K : ℤ) ≤ ⌈u⌉ := by
    exact_mod_cast hu.trans (Int.le_ceil u)
  have hn : ramificationCutoff T K ≤ ⌈u⌉.toNat := by
    simpa using Int.toNat_le_toNat hc
  have hz : 0 ≤ ⌈u⌉ := (Int.natCast_nonneg _).trans hc
  change lowerGroupInt T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⌈u⌉ = ⊥
  rw [lowerGroupInt, ite_eq_right (not_lt.mpr hz)]
  exact lowerRamificationGroup_eq_bot_of_cutoff T K _ hn

/-- Eventual triviality is proved from the existing lower-group theorem
and the inverse identities, with no supplied cutoff hypothesis. -/
theorem exists_upperRamificationGroup_eq_bot :
    ∃ b : ℝ, ∀ v ≥ b, upperRamificationGroup T K v = ⊥ := by
  refine ⟨herbrandPhi T K (ramificationCutoff T K), fun v hv => ?_⟩
  have h := (herbrandPsi_strictMono T K).monotone hv
  rw [herbrandPsi_herbrandPhi] at h
  exact lowerRamificationGroupReal_eq_bot_of_cutoff T K h

variable (F)

/-- Every algebraic p-adic field has this upper filtration, without an
extra realization hypothesis, through the published canonical constructor. -/
def canonicalUpperRamificationGroup (v : ℝ) :
    Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  upperRamificationGroup F.canonicalTopologicalData K v

end Langlands.Ramification.Padic
