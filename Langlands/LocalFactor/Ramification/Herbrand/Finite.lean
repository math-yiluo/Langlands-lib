import Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite
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
    lowerRamificationGroupReal T K i = lowerRamificationGroupInt T K i :=
  Local.lowerRamificationGroupReal_int T.toLocalData K i

@[simp] theorem lowerRamificationGroupReal_nat (i : ℕ) :
    lowerRamificationGroupReal T K i = lowerRamificationGroup T K i :=
  Local.lowerRamificationGroupReal_nat T.toLocalData K i

@[simp] theorem lowerRamificationGroupReal_neg_one :
    lowerRamificationGroupReal T K (-1) = ⊤ :=
  Local.lowerRamificationGroupReal_neg_one T.toLocalData K

@[simp] theorem lowerRamificationGroupReal_zero :
    lowerRamificationGroupReal T K 0 = inertia T K :=
  Local.lowerRamificationGroupReal_zero T.toLocalData K

instance lowerRamificationGroupInt_normal (i : ℤ) :
    (lowerRamificationGroupInt T K i).Normal :=
  Local.lowerRamificationGroupInt_normal T.toLocalData K i

instance lowerRamificationGroupReal_normal (u : ℝ) :
    (lowerRamificationGroupReal T K u).Normal :=
  Local.lowerRamificationGroupReal_normal T.toLocalData K u

theorem lowerRamificationGroupInt_antitone :
    Antitone (lowerRamificationGroupInt T K) :=
  Local.lowerRamificationGroupInt_antitone T.toLocalData K

theorem lowerRamificationGroupReal_antitone :
    Antitone (lowerRamificationGroupReal T K) :=
  Local.lowerRamificationGroupReal_antitone T.toLocalData K

/-- The actual order of the published lower group. -/
def lowerGroupOrder (i : ℕ) : ℕ := Nat.card (lowerRamificationGroup T K i)

theorem lowerGroupOrder_pos (i : ℕ) : 0 < lowerGroupOrder T K i :=
  Local.lowerGroupOrder_pos T.toLocalData K i

theorem lowerGroupOrder_one_le (i : ℕ) : 1 ≤ lowerGroupOrder T K i :=
  Local.lowerGroupOrder_one_le T.toLocalData K i

/-- An intrinsic cutoff chosen from the proved eventual triviality theorem. -/
def ramificationCutoff : ℕ := (exists_lowerRamificationGroup_eq_bot T K).choose

theorem lowerRamificationGroup_eq_bot_of_cutoff (i : ℕ)
    (hi : ramificationCutoff T K ≤ i) : lowerRamificationGroup T K i = ⊥ :=
  Local.lowerRamificationGroup_eq_bot_of_cutoff T.toLocalData K i hi

theorem lowerGroupOrder_tail (i : ℕ) (hi : ramificationCutoff T K ≤ i) :
    lowerGroupOrder T K (i + 1) = 1 :=
  Local.lowerGroupOrder_tail T.toLocalData K i hi

/-- Serre's real Herbrand function, extended by the identity below `-1`.
The positive branch is the floor formula, proved below. -/
def herbrandPhi (u : ℝ) : ℝ :=
  Herbrand.polygon (lowerGroupOrder T K) (ramificationCutoff T K) u

theorem herbrandPhi_floor {u : ℝ} (hu : 0 ≤ u) :
    herbrandPhi T K u =
      ((∑ i ∈ Finset.range ⌊u⌋₊, (lowerGroupOrder T K (i + 1) : ℝ)) +
        (u - ⌊u⌋₊) * lowerGroupOrder T K (⌊u⌋₊ + 1)) /
      lowerGroupOrder T K 0 :=
  Local.herbrandPhi_floor T.toLocalData K hu

theorem herbrandPhi_of_nonpos {u : ℝ} (hu : u ≤ 0) : herbrandPhi T K u = u :=
  Local.herbrandPhi_of_nonpos T.toLocalData K hu

@[simp] theorem herbrandPhi_zero : herbrandPhi T K 0 = 0 :=
  Local.herbrandPhi_zero T.toLocalData K

@[simp] theorem herbrandPhi_neg_one : herbrandPhi T K (-1) = -1 :=
  Local.herbrandPhi_neg_one T.toLocalData K

theorem herbrandPhi_continuous : Continuous (herbrandPhi T K) :=
  Local.herbrandPhi_continuous T.toLocalData K

theorem herbrandPhi_strictMono : StrictMono (herbrandPhi T K) :=
  Local.herbrandPhi_strictMono T.toLocalData K

theorem herbrandPhi_surjective : Function.Surjective (herbrandPhi T K) :=
  Local.herbrandPhi_surjective T.toLocalData K

/-- The constructed order isomorphism of the real indexing line. -/
def herbrandOrderIso : ℝ ≃o ℝ :=
  Herbrand.polygonOrderIso (lowerGroupOrder T K) (ramificationCutoff T K)
    (lowerGroupOrder_one_le T K)

/-- The genuine inverse Herbrand function. -/
def herbrandPsi (v : ℝ) : ℝ := (herbrandOrderIso T K).symm v

@[simp] theorem herbrandOrderIso_apply (u : ℝ) :
    herbrandOrderIso T K u = herbrandPhi T K u :=
  Local.herbrandOrderIso_apply T.toLocalData K u

@[simp] theorem herbrandPhi_herbrandPsi (v : ℝ) :
    herbrandPhi T K (herbrandPsi T K v) = v :=
  Local.herbrandPhi_herbrandPsi T.toLocalData K v

@[simp] theorem herbrandPsi_herbrandPhi (u : ℝ) :
    herbrandPsi T K (herbrandPhi T K u) = u :=
  Local.herbrandPsi_herbrandPhi T.toLocalData K u

theorem herbrandPsi_continuous : Continuous (herbrandPsi T K) :=
  Local.herbrandPsi_continuous T.toLocalData K

theorem herbrandPsi_strictMono : StrictMono (herbrandPsi T K) :=
  Local.herbrandPsi_strictMono T.toLocalData K

theorem herbrandPsi_of_nonpos {v : ℝ} (hv : v ≤ 0) : herbrandPsi T K v = v :=
  Local.herbrandPsi_of_nonpos T.toLocalData K hv

@[simp] theorem herbrandPsi_zero : herbrandPsi T K 0 = 0 :=
  Local.herbrandPsi_zero T.toLocalData K

@[simp] theorem herbrandPsi_neg_one : herbrandPsi T K (-1) = -1 :=
  Local.herbrandPsi_neg_one T.toLocalData K

/-- The same maps restricted to the original half-line `[-1,infinity)`. -/
def herbrandHalfLineOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) :=
  Herbrand.halfLineOrderIso _ (ramificationCutoff T K) (lowerGroupOrder_one_le T K)

theorem herbrandPhi_pos {u : ℝ} (hu : 0 < u) : 0 < herbrandPhi T K u :=
  Local.herbrandPhi_pos T.toLocalData K hu

theorem herbrandPsi_pos {v : ℝ} (hv : 0 < v) : 0 < herbrandPsi T K v :=
  Local.herbrandPsi_pos T.toLocalData K hv

/-- Actual upper numbering, obtained by reindexing the published lower groups
by the constructed inverse Herbrand function. -/
def upperRamificationGroup (v : ℝ) : Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  lowerRamificationGroupReal T K (herbrandPsi T K v)

theorem upperRamificationGroup_eq_lower (v : ℝ) :
    upperRamificationGroup T K v =
      lowerRamificationGroupInt T K ⌈herbrandPsi T K v⌉ :=
  Local.upperRamificationGroup_eq_lower T.toLocalData K v

@[simp] theorem upperRamificationGroup_phi (u : ℝ) :
    upperRamificationGroup T K (herbrandPhi T K u) =
      lowerRamificationGroupReal T K u :=
  Local.upperRamificationGroup_phi T.toLocalData K u

@[simp] theorem upperRamificationGroup_neg_one : upperRamificationGroup T K (-1) = ⊤ :=
  Local.upperRamificationGroup_neg_one T.toLocalData K

@[simp] theorem upperRamificationGroup_zero : upperRamificationGroup T K 0 = inertia T K :=
  Local.upperRamificationGroup_zero T.toLocalData K

instance upperRamificationGroup_normal (v : ℝ) :
    (upperRamificationGroup T K v).Normal :=
  Local.upperRamificationGroup_normal T.toLocalData K v

theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup T K) :=
  Local.upperRamificationGroup_antitone T.toLocalData K

theorem lowerRamificationGroupReal_eq_bot_of_cutoff {u : ℝ}
    (hu : (ramificationCutoff T K : ℝ) ≤ u) :
    lowerRamificationGroupReal T K u = ⊥ :=
  Local.lowerRamificationGroupReal_eq_bot_of_cutoff T.toLocalData K hu

/-- Eventual triviality is proved from the existing lower-group theorem
and the inverse identities, with no supplied cutoff hypothesis. -/
theorem exists_upperRamificationGroup_eq_bot :
    ∃ b : ℝ, ∀ v ≥ b, upperRamificationGroup T K v = ⊥ :=
  Local.exists_upperRamificationGroup_eq_bot T.toLocalData K

variable (F)

/-- Every algebraic p-adic field has this upper filtration, without an
extra realization hypothesis, through the published canonical constructor. -/
def canonicalUpperRamificationGroup (v : ℝ) :
    Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  upperRamificationGroup F.canonicalTopologicalData K v

end Langlands.Ramification.Padic
