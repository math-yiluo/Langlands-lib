import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Characters of finite groups of prime-to-characteristic order -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.PrimeToCharacteristicCharacters

variable (K : Type u) [Field K] (p : ℕ) [ExpChar K p]

/-- A positive integer prime to the characteristic exponent is nonzero in the field. -/
lemma cast_ne_zero_of_coprime (n : ℕ) (hn : 0 < n) (h : Nat.Coprime n p) :
    (n : K) ≠ 0 := by
  cases ‹ExpChar K p› with
  | zero => exact_mod_cast hn.ne'
  | prime hp =>
    intro hzero
    exact (hp.coprime_iff_not_dvd.mp h.symm) ((CharP.cast_eq_zero_iff K p n).mp hzero)

variable [IsSepClosed K] (M : Type v) [CommGroup M] [Finite M]

/-- A separably closed field has enough roots for a finite prime-to-characteristic group. -/
lemma hasEnoughRootsOfUnity (h : Nat.Coprime (Nat.card M) p) :
    HasEnoughRootsOfUnity K (Monoid.exponent M) := by
  have : NeZero ((Monoid.exponent M : ℕ) : K) :=
    ⟨cast_ne_zero_of_coprime K p (Monoid.exponent M)
      (Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite)
      (h.of_dvd_left Group.exponent_dvd_nat_card)⟩
  infer_instance

/-- Every nonidentity point of a finite prime-to-characteristic group is detected by a character. -/
theorem exists_apply_ne_one (h : Nat.Coprime (Nat.card M) p) {a : M} (ha : a ≠ 1) :
    ∃ χ : M →* Kˣ, χ a ≠ 1 := by
  have := hasEnoughRootsOfUnity K p M h
  exact CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity M K ha

/-- Characters distinguish any two points of a finite prime-to-characteristic group. -/
theorem forall_apply_eq_apply_iff (h : Nat.Coprime (Nat.card M) p) {a b : M} :
    (∀ χ : M →* Kˣ, χ a = χ b) ↔ a = b := by
  have := hasEnoughRootsOfUnity K p M h
  exact CommGroup.forall_apply_eq_apply_iff M

/-- One character for each group element suffices to distinguish all points. -/
theorem exists_separating_family (h : Nat.Coprime (Nat.card M) p) :
    ∃ χ : M → M →* Kˣ, Function.Injective (fun a : M => fun i : M => χ i a) := by
  classical
  have hex : ∀ a : M, ∃ χ : M →* Kˣ, a ≠ 1 → χ a ≠ 1 := by
    intro a
    by_cases ha : a = 1
    · exact ⟨1, fun h => (h ha).elim⟩
    · obtain ⟨χ, hχ⟩ := exists_apply_ne_one K p M h ha
      exact ⟨χ, fun _ => hχ⟩
  choose χ hχ using hex
  refine ⟨χ, fun a b hab => ?_⟩
  by_contra hne
  apply hχ (a * b⁻¹) (fun h => hne (mul_inv_eq_one.mp h))
  have hval : χ (a * b⁻¹) a = χ (a * b⁻¹) b := congrFun hab (a * b⁻¹)
  rw [map_mul, map_inv, hval, mul_inv_cancel]

end Langlands.GroupScheme.PrimeToCharacteristicCharacters
