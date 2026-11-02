import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units

/-! # Prime-power cyclotomic Galois groups -/

universe u v

namespace Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois

/-- Units modulo `p^(n+k)` that are one modulo `p^k`. -/
def principalUnits (p n k : ℕ) : Subgroup (ZMod (p ^ (n + k)))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow p (Nat.le_add_left k n))).ker

/-- The degree of a cyclotomic extension divides the totient of its order. -/
theorem finrank_dvd_totient {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ} [NeZero m]
    [IsCyclotomicExtension {m} K L] : Module.finrank K L ∣ m.totient := by
  let := IsCyclotomicExtension.finiteDimensional {m} K L
  let := IsCyclotomicExtension.isGalois {m} K L
  let hζ := IsCyclotomicExtension.zeta_spec m K L
  have h := Subgroup.card_dvd_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)
  rw [IsGalois.card_aut_eq_finrank K L] at h
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using h

/-- The principal-unit kernel has the expected prime-power order. -/
theorem card_principalUnits {p n k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card (principalUnits p n k) = p ^ n := by
  classical
  let : NeZero (p ^ (n + k)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let f := ZMod.unitsMap (pow_dvd_pow p (Nat.le_add_left k n))
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    (ZMod.unitsMap_surjective _), Subgroup.card_top] at hc
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hc
  have ht : (p ^ (n + k)).totient = p ^ n * (p ^ k).totient := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [show n + (j + 1) = n + j + 1 by omega,
      Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp, pow_add, mul_assoc]
  rw [ht] at hc
  apply mul_right_cancel₀ (Nat.totient_pos.mpr (pow_pos hp.pos k)).ne'
  simpa only [principalUnits, Nat.card_eq_fintype_card] using hc

/-- In the stable range, the principal-unit kernel is cyclic. -/
theorem isCyclic_principalUnits {p n k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hkp : k + 2 ≤ p * k) : IsCyclic (principalUnits p n k) := by
  classical
  let : NeZero (p ^ (n + k)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have ho : orderOf (1 + p ^ k : ZMod (p ^ (n + k))) = p ^ n := by
    simpa only [Int.cast_one, mul_one] using
      ZMod.orderOf_one_add_mul_prime_pow hp k hk hkp 1
        (by
          intro h
          apply hp.ne_one
          simpa using Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h) n
  have ha : IsUnit (1 + p ^ k : ZMod (p ^ (n + k))) :=
    (orderOf_pos_iff.mp (ho ▸ pow_pos hp.pos n)).isUnit
  have hm : ha.unit ∈ principalUnits p n k := by
    apply Units.ext
    change (ZMod.castHom (pow_dvd_pow p (Nat.le_add_left k n))
      (ZMod (p ^ k))) (ha.unit : ZMod (p ^ (n + k))) = 1
    rw [ha.unit_spec, map_add, map_one, map_pow, map_natCast]
    simp only [← Nat.cast_pow, ZMod.natCast_self, add_zero]
  apply isCyclic_of_orderOf_eq_card (⟨ha.unit, hm⟩ : principalUnits p n k)
  rw [Subgroup.orderOf_mk, ← orderOf_units, ha.unit_spec, ho,
    card_principalUnits hp hk]

/-- Base-field roots of unity force the cyclotomic character into principal units. -/
theorem autToPow_mem_principalUnits {B : Type u} {E : Type v}
    [Field B] [Field E] [Algebra B E] {p n k : ℕ}
    [NeZero (p ^ (n + k))]
    [IsCyclotomicExtension {p ^ (n + k)} B E]
    (hp : p.Prime) {ξ : B} (hξ : IsPrimitiveRoot ξ (p ^ k))
    (σ : E ≃ₐ[B] E) :
    (IsCyclotomicExtension.zeta_spec (p ^ (n + k)) B E).autToPow B σ ∈
      principalUnits p n k := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let ζ := IsCyclotomicExtension.zeta (p ^ (n + k)) B E
  have hζ : IsPrimitiveRoot ζ (p ^ (n + k)) :=
    IsCyclotomicExtension.zeta_spec (p ^ (n + k)) B E
  have hζn : IsPrimitiveRoot (ζ ^ (p ^ n)) (p ^ k) := by
    have h := hζ.pow_of_dvd (pow_ne_zero n hp.ne_zero)
      (pow_dvd_pow p (Nat.le_add_right n k))
    simpa only [pow_add, Nat.mul_div_cancel_left _ (pow_pos hp.pos n)] using h
  obtain ⟨i, _, hi⟩ :=
    (hξ.map_of_injective (algebraMap B E).injective).eq_pow_of_pow_eq_one hζn.pow_eq_one
  have hfix : σ (ζ ^ (p ^ n)) = ζ ^ (p ^ n) := by
    rw [← hi, map_pow, σ.commutes]
  have he : (ζ ^ (p ^ n)) ^ (hζ.autToPow B σ : ZMod (p ^ (n + k))).val =
      (ζ ^ (p ^ n)) ^ 1 := by
    rw [pow_one, pow_right_comm, hζ.autToPow_spec B σ, ← map_pow, hfix]
  have hmod := (hζn.isOfFinOrder (pow_ne_zero k hp.ne_zero)).pow_eq_pow_iff_modEq.mp he
  rw [← hζn.eq_orderOf] at hmod
  apply Units.ext
  change (ZMod.castHom (pow_dvd_pow p (Nat.le_add_left k n)) (ZMod (p ^ k)))
    (hζ.autToPow B σ : ZMod (p ^ (n + k))) = 1
  rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ 1 (p ^ k)).mpr hmod

/-- A suitable base-field root makes the cyclotomic Galois group cyclic of prime-power degree. -/
theorem isCyclic_and_finrank_eq_pow {B : Type u} {E : Type v}
    [Field B] [Field E] [Algebra B E] {p n k : ℕ}
    [IsCyclotomicExtension {p ^ (n + k)} B E]
    (hp : p.Prime) (hk : k ≠ 0) (hkp : k + 2 ≤ p * k)
    {ξ : B} (hξ : IsPrimitiveRoot ξ (p ^ k)) :
    IsCyclic (E ≃ₐ[B] E) ∧ ∃ e, Module.finrank B E = p ^ e := by
  let : NeZero (p ^ (n + k)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let := IsCyclotomicExtension.finiteDimensional {p ^ (n + k)} B E
  let := IsCyclotomicExtension.isGalois {p ^ (n + k)} B E
  let := isCyclic_principalUnits (n := n) hp hk hkp
  let χ := ((IsCyclotomicExtension.zeta_spec (p ^ (n + k)) B E).autToPow B).codRestrict
    (principalUnits p n k) (autToPow_mem_principalUnits hp hξ)
  have hχ : Function.Injective χ := by
    intro σ τ h
    apply (IsCyclotomicExtension.zeta_spec (p ^ (n + k)) B E).autToPow_injective B
    exact congrArg Subtype.val h
  refine ⟨isCyclic_of_injective χ hχ, ?_⟩
  have hd := Subgroup.card_dvd_of_injective χ hχ
  rw [card_principalUnits hp hk, IsGalois.card_aut_eq_finrank B E] at hd
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  exact ⟨e, he⟩

end Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois
