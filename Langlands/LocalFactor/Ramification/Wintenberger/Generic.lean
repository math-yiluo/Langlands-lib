import FontaineWintenberger.Ramification.Upper.Basic
import FontaineWintenberger.Ramification.Herbrand.Affine
import Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite

/-!
# The generic ramification filtrations of the two libraries agree

For a group acting on a local ring, the lower ramification groups of the FontaineWintenberger
library at the maximal ideal are the Library's integer lower groups. For a local-field
realization `T` of a finite extension `L` of `K₀` and an intermediate field `K`, acting on the
integer ring of `T`, the Herbrand function of the FontaineWintenberger library (an integral of
lower-group orders) is the Library's polygon `Local.herbrandPhi T K`, its inverse is
`Local.herbrandPsi T K` on `[-1, ∞)`, and the upper groups agree at every real index.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

section Generic

variable (R : Type*) (G : Type*) [CommRing R] [IsLocalRing R] [Group G] [MulSemiringAction G R]

/-- At the maximal ideal of a local ring, the integer lower groups of the two libraries are the
same subgroup: both are inertia subgroups of a power of the maximal ideal, and both are the
whole group at negative indices. -/
theorem lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt (n : ℤ) :
    FontaineWintenberger.lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n =
      Langlands.Ramification.lowerGroupInt R G n := by
  rcases lt_or_ge n 0 with h | h
  · have h0 : (n + 1).toNat = 0 := by omega
    rw [Langlands.Ramification.lowerGroupInt, ite_eq_left h,
      FontaineWintenberger.lowerRamificationGroup, h0, pow_zero, Ideal.one_eq_top]
    ext g
    simp
  · have h0 : (n + 1).toNat = n.toNat + 1 := by omega
    rw [Langlands.Ramification.lowerGroupInt, ite_eq_right (not_lt.mpr h),
      FontaineWintenberger.lowerRamificationGroup, h0]
    rfl

end Generic

section Supplied

universe u₀ uK uL

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {L : Type uL} [Field L] [Algebra K₀ L]
  (T : LocalField.TopologicalData K₀ L) (K : Type uK) [Field K] [Algebra K₀ K]
  [Algebra K L] [IsScalarTower K₀ K L]

/-- The integer ring of a local-field realization is a discrete valuation ring. -/
theorem integers_isDiscreteValuationRing : IsDiscreteValuationRing T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The FontaineWintenberger lower groups for the action on the integer ring of `T` are the
Library's integer lower groups. -/
theorem lowerRamificationGroup_eq_lowerRamificationGroupInt (n : ℤ) :
    letI := Local.integerAction T K
    FontaineWintenberger.lowerRamificationGroup (L ≃ₐ[K] L)
        (IsLocalRing.maximalIdeal T.Integers) n =
      Local.lowerRamificationGroupInt T K n := by
  let := Local.integerAction T K
  exact lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt T.Integers (L ≃ₐ[K] L) n

/-- The orders of the lower groups at natural indices agree. -/
theorem card_lowerRamificationGroup_eq_lowerGroupOrder (m : ℕ) :
    letI := Local.integerAction T K
    Nat.card (FontaineWintenberger.lowerRamificationGroup (L ≃ₐ[K] L)
        (IsLocalRing.maximalIdeal T.Integers) (m : ℤ)) =
      Local.lowerGroupOrder T K m := by
  let := Local.integerAction T K
  rw [lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt, Langlands.Ramification.lowerGroupInt_nat]
  rfl

variable [FiniteDimensional K₀ L]

omit [ValuativeRel K₀] [TopologicalSpace K₀] in
include K₀ in
/-- The automorphism group of `L` over an intermediate field of a finite extension is finite. -/
theorem automorphismGroup_finite : Finite (L ≃ₐ[K] L) := by
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  infer_instance

/-- **The Herbrand functions agree.** The integral of lower-group orders of the
FontaineWintenberger library is the Library's polygon, at every real argument. -/
theorem herbrandFunction_eq_herbrandPhi (t : ℝ) :
    letI := Local.integerAction T K
    letI := integers_isDiscreteValuationRing T
    letI := automorphismGroup_finite (K₀ := K₀) (L := L) K
    FontaineWintenberger.herbrandFunction (R := T.Integers) (L ≃ₐ[K] L) t =
      Local.herbrandPhi T K t := by
  let := Local.integerAction T K
  let := integers_isDiscreteValuationRing T
  let := automorphismGroup_finite (K₀ := K₀) (L := L) K
  set g := Local.lowerGroupOrder T K with hg
  have hcard : ∀ m : ℕ, (Nat.card (FontaineWintenberger.lowerRamificationGroup (L ≃ₐ[K] L)
      (IsLocalRing.maximalIdeal T.Integers) (m : ℤ)) : ℝ) = g m := fun m => by
    rw [card_lowerRamificationGroup_eq_lowerGroupOrder]
  have hcard1 : ∀ n : ℕ, (Nat.card (FontaineWintenberger.lowerRamificationGroup (L ≃ₐ[K] L)
      (IsLocalRing.maximalIdeal T.Integers) ((n : ℤ) + 1)) : ℝ) = g (n + 1) := fun n => by
    rw [← hcard (n + 1)]
    push_cast
    rfl
  have hcard0 := hcard 0
  simp only [Nat.cast_zero] at hcard0
  have htail := Local.lowerGroupOrder_tail T K
  have hlib : ∀ (n : ℕ) {u : ℝ}, (n : ℝ) ≤ u → u ≤ n + 1 →
      Local.herbrandPhi T K u = Local.herbrandPhi T K n + (u - n) * g (n + 1) / g 0 := by
    intro n u hlo hhi
    have h1 := Herbrand.polygon_on_unit_interval g (Local.ramificationCutoff T K) htail n hlo hhi
    have h2 := Herbrand.polygon_on_unit_interval g (Local.ramificationCutoff T K) htail n le_rfl
      (by linarith)
    change Herbrand.polygon g _ u = Herbrand.polygon g _ n + _
    rw [h1, h2]
    ring
  have hnat : ∀ n : ℕ, FontaineWintenberger.herbrandFunction (R := T.Integers) (L ≃ₐ[K] L) n =
      Local.herbrandPhi T K n := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, Local.herbrandPhi_zero]
      exact FontaineWintenberger.herbrandFunction_of_nonpos _ le_rfl
    | succ n ih =>
      rw [FontaineWintenberger.herbrandFunction_affine _ n (by push_cast; linarith)
        (by push_cast; linarith), hlib n (by push_cast; linarith) (by push_cast; linarith), ih,
        hcard1, hcard0]
  rcases le_or_gt t 0 with ht | ht
  · rw [FontaineWintenberger.herbrandFunction_of_nonpos _ ht, Local.herbrandPhi_of_nonpos T K ht]
  · set n := ⌊t⌋₊
    have hlo : (n : ℝ) ≤ t := Nat.floor_le ht.le
    have hhi : t ≤ n + 1 := (Nat.lt_floor_add_one t).le
    rw [FontaineWintenberger.herbrandFunction_affine _ n hlo hhi, hlib n hlo hhi, hnat, hcard1, hcard0]

/-- The inverse Herbrand functions agree on `[-1, ∞)`; below `-1` the FontaineWintenberger
inverse is clamped at `-1`, the Library's is not. -/
theorem inverseHerbrandFunction_eq_herbrandPsi {v : ℝ} (hv : -1 ≤ v) :
    letI := Local.integerAction T K
    letI := integers_isDiscreteValuationRing T
    letI := automorphismGroup_finite (K₀ := K₀) (L := L) K
    FontaineWintenberger.inverseHerbrandFunction (R := T.Integers) (L ≃ₐ[K] L) v =
      Local.herbrandPsi T K v := by
  let := Local.integerAction T K
  let := integers_isDiscreteValuationRing T
  let := automorphismGroup_finite (K₀ := K₀) (L := L) K
  apply (Local.herbrandPhi_strictMono T K).injective
  rw [Local.herbrandPhi_herbrandPsi, ← herbrandFunction_eq_herbrandPhi,
    FontaineWintenberger.herbrandFunction_inverseHerbrandFunction _ hv]

/-- **The finite upper groups agree** at every real index. -/
theorem upperRamificationGroup_eq_upperRamificationGroup (v : ℝ) :
    letI := Local.integerAction T K
    letI := integers_isDiscreteValuationRing T
    letI := automorphismGroup_finite (K₀ := K₀) (L := L) K
    FontaineWintenberger.upperRamificationGroup (R := T.Integers) (L ≃ₐ[K] L) v =
      Local.upperRamificationGroup T K v := by
  let := Local.integerAction T K
  let := integers_isDiscreteValuationRing T
  let := automorphismGroup_finite (K₀ := K₀) (L := L) K
  rw [Local.upperRamificationGroup_eq_lower, FontaineWintenberger.upperRamificationGroup,
    FontaineWintenberger.lowerRamificationGroupReal, ← lowerRamificationGroup_eq_lowerRamificationGroupInt]
  rcases le_or_gt (-1) v with hv | hv
  · rw [inverseHerbrandFunction_eq_herbrandPsi T K hv]
  · have hψ : FontaineWintenberger.inverseHerbrandFunction (R := T.Integers) (L ≃ₐ[K] L) v = -1 := by
      have h1 : FontaineWintenberger.inverseHerbrandFunction (R := T.Integers) (L ≃ₐ[K] L) v =
          FontaineWintenberger.inverseHerbrandFunction (R := T.Integers) (L ≃ₐ[K] L) (-1) := by
        simp only [FontaineWintenberger.inverseHerbrandFunction, max_eq_right hv.le, max_self]
      rw [h1]
      exact FontaineWintenberger.inverseHerbrandFunction_of_nonpos _ le_rfl (by norm_num)
    have hlt : Local.herbrandPsi T K v < -1 := by
      simpa using Local.herbrandPsi_strictMono T K hv
    rw [hψ, lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt,
      lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt, Langlands.Ramification.lowerGroupInt,
      Langlands.Ramification.lowerGroupInt, ite_eq_left (by norm_num),
      ite_eq_left (by rw [Int.ceil_lt_iff]; push_cast; linarith)]

end Supplied

end Langlands.Ramification.Wintenberger
