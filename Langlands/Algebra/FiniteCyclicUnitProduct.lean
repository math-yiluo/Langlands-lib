import Langlands.Algebra.CyclicSemilinearFixedSpan
import Mathlib.Data.Fintype.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-! Cyclic products on the units of finite commutative rings. -/

noncomputable section

namespace Langlands

universe u

variable {S : Type u} [CommRing S]

/-- Applying `σ` to the first `l` conjugates cyclically permutes their product
when `σ ^ l = 1`. -/
theorem ringAut_prod_powers_fixed (σ : RingAut S) {l : ℕ} (hσ : σ ^ l = 1) (a : S) :
    σ (∏ i : Fin l, (σ ^ (i : ℕ)) a) = ∏ i : Fin l, (σ ^ (i : ℕ)) a := by
  cases l with
  | zero => simp
  | succ l =>
    calc
      _ = (∏ i : Fin l, σ ((σ ^ (i : ℕ)) a)) * (σ ^ (l + 1)) a := by
        rw [map_prod, Fin.prod_univ_castSucc, pow_succ', RingAut.mul_apply]
        rfl
      _ = a * (∏ i : Fin l, σ ((σ ^ (i : ℕ)) a)) := by rw [hσ, RingAut.one_apply, mul_comm]
      _ = _ := by rw [Fin.prod_univ_succ]; simp [pow_succ']

/-- The additive operator obtained by applying a ring automorphism and then
multiplying by a specified unit. -/
def cyclicUnitOperator (σ : RingAut S) (u : Sˣ) : AddMonoid.End S :=
  (AddMonoidHom.mulLeft (u : S)).comp σ.toAddMonoidHom

@[simp] theorem cyclicUnitOperator_apply (σ : RingAut S) (u : Sˣ) (a : S) :
    cyclicUnitOperator σ u a = (u : S) * σ a := rfl

private theorem cyclicUnitOperator_pow_apply (σ : RingAut S) (u : Sˣ) (l : ℕ) (a : S) :
    (cyclicUnitOperator σ u ^ l) a = (∏ i : Fin l, (σ ^ (i : ℕ)) (u : S)) * (σ ^ l) a := by
  induction l generalizing a with
  | zero => simp
  | succ l ih =>
    rw [pow_succ]
    change (cyclicUnitOperator σ u ^ l) (cyclicUnitOperator σ u a) = _
    rw [ih, cyclicUnitOperator_apply, map_mul,
      Fin.prod_univ_castSucc, mul_assoc, pow_succ σ, RingAut.mul_apply]
    rfl

private theorem pow_mem_ideal_iff_of_fixed {σ : RingAut S} {u : Sˣ} {x : S}
    (hx : (u : S) * σ x = x) (I : Ideal S) (i : ℕ) : (σ ^ i) x ∈ I ↔ x ∈ I := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have he : (σ ^ i) (u : S) * (σ ^ (i + 1)) x = (σ ^ i) x := by
      simpa only [pow_succ σ i, RingAut.mul_apply, map_mul] using congrArg (σ ^ i) hx
    rw [← ih, ← he]
    exact (I.unit_mul_mem_iff_mem (u.isUnit.map (σ ^ i).toRingHom)).symm

/-- If the product of the first `l` conjugates of `u` is one, then the
semilinear map `x ↦ u * σ x` has a fixed unit. The cyclic conjugates of one
scalar must have pairwise unit differences. -/
theorem exists_cyclicUnitOperator_fixed_unit [Finite S] (σ : RingAut S) {l : ℕ}
    (hl : 0 < l) (hσ : σ ^ l = 1) (a : S)
    (ha : Pairwise fun i j : Fin l => IsUnit ((σ ^ (i : ℕ)) a - (σ ^ (j : ℕ)) a))
    (u : Sˣ) (hu : (∏ i : Fin l, (σ ^ (i : ℕ)) (u : S)) = 1) :
    ∃ x : Sˣ, (u : S) * σ (x : S) = x := by
  classical
  let D := cyclicUnitOperator σ u
  have hD : D ^ l = 1 := by
    ext x
    simp only [D, cyclicUnitOperator_pow_apply, hσ, hu, RingAut.one_apply, one_mul,
      AddMonoid.End.one_apply]
  have hsmul (b x : S) : D (b • x) = σ b • D x := by
    simp [D, smul_eq_mul, mul_left_comm]
  have hspan := span_cyclicSemilinear_fixed_eq_top σ D hl hD hsmul a ha
  let V := {x : S // (u : S) * σ x = x}
  let : Nonempty V := ⟨⟨0, by simp⟩⟩
  let : Finite (MaximalSpectrum S) := Finite.of_injective
    (fun m : MaximalSpectrum S => (m.asIdeal : Set S))
    (fun _ _ h => MaximalSpectrum.ext (SetLike.coe_injective h))
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  let nonzeroAt (x : S) : Finset (MaximalSpectrum S) :=
    Finset.univ.filter fun m => x ∉ m.asIdeal
  have nonzeroAt_iff (x : S) (m : MaximalSpectrum S) : m ∈ nonzeroAt x ↔ x ∉ m.asIdeal := by
    simp [nonzeroAt]
  obtain ⟨y, hy⟩ := Finite.exists_max (fun x : V => (nonzeroAt x.val).card)
  suffices hunit : IsUnit y.val from ⟨hunit.unit, by simpa using y.property⟩
  by_contra hn
  obtain ⟨I, hI, hyI⟩ := exists_max_ideal_of_mem_nonunits hn
  have hspanI : ∃ z : V, z.val ∉ I := by
    by_contra! hnone
    have h : Submodule.span S {x : S | D x = x} ≤ I := by
      apply Submodule.span_le.mpr
      exact fun x hx => hnone ⟨x, hx⟩
    rw [hspan] at h
    exact hI.ne_top (top_unique h)
  obtain ⟨z, hz⟩ := hspanI
  obtain ⟨a₀, ha₀⟩ := Ideal.pi_quotient_surjective
    (I := fun m : MaximalSpectrum S => m.asIdeal) (fun _ _ h => MaximalSpectrum.isCoprime_of_ne h)
    (fun m => if y.val ∈ m.asIdeal then 1 else 0)
  let b := ∏ i : Fin l, (σ ^ (i : ℕ)) a₀
  have hb : σ b = b := ringAut_prod_powers_fixed σ hσ a₀
  have hb_res (m : MaximalSpectrum S) :
      Ideal.Quotient.mk m.asIdeal b = if y.val ∈ m.asIdeal then 1 else 0 := by
    let q := Ideal.Quotient.mk m.asIdeal
    have hi (i : Fin l) : q ((σ ^ (i : ℕ)) a₀) = if y.val ∈ m.asIdeal then 1 else 0 := by
      let f := (σ ^ (i : ℕ)).toRingHom
      let J := m.asIdeal.comap f
      let : m.asIdeal.IsMaximal := m.isMaximal
      let m' : MaximalSpectrum S := ⟨J,
        Ideal.comap_isMaximal_of_surjective f (σ ^ (i : ℕ)).surjective⟩
      have hy' : y.val ∈ J ↔ y.val ∈ m.asIdeal :=
        pow_mem_ideal_iff_of_fixed y.property m.asIdeal i.val
      let g : S ⧸ J →+* S ⧸ m.asIdeal :=
        Ideal.Quotient.lift J (q.comp f) (fun _ h => Ideal.Quotient.eq_zero_iff_mem.mpr h)
      have h := congrArg g (ha₀ m')
      change q (f a₀) = g (if y.val ∈ J then 1 else 0) at h
      rw [hy'] at h
      change q (f a₀) = _
      simpa only [apply_ite g, map_one, map_zero] using h
    change q (∏ i : Fin l, (σ ^ (i : ℕ)) a₀) = _
    rw [map_prod]
    simp only [hi]
    by_cases hm : y.val ∈ m.asIdeal
    · simp [hm]
    · simp [hm, hl.ne']
  let w : V := ⟨y.val + b * z.val, by
    rw [map_add, map_mul, hb, mul_add, mul_left_comm (u : S) b, y.property, z.property]⟩
  have hw₁ : nonzeroAt y.val ⊆ nonzeroAt w.val := by
    intro m hm
    rw [nonzeroAt_iff] at hm ⊢
    have h : Ideal.Quotient.mk m.asIdeal w.val = Ideal.Quotient.mk m.asIdeal y.val := by
      change Ideal.Quotient.mk m.asIdeal (y.val + b * z.val) = _
      simp [hb_res, hm]
    intro ha
    exact hm (Ideal.Quotient.eq_zero_iff_mem.mp (h ▸ Ideal.Quotient.eq_zero_iff_mem.mpr ha))
  let m : MaximalSpectrum S := ⟨I, hI⟩
  have hw₂ : m ∈ nonzeroAt w.val := by
    rw [nonzeroAt_iff]
    have hbI : Ideal.Quotient.mk I b = 1 := (hb_res m).trans (by simp [m, hyI])
    have h : Ideal.Quotient.mk I w.val = Ideal.Quotient.mk I z.val := by
      change Ideal.Quotient.mk I (y.val + b * z.val) = _
      rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hyI, hbI, zero_add, one_mul]
    intro ha
    exact hz (Ideal.Quotient.eq_zero_iff_mem.mp (h ▸ Ideal.Quotient.eq_zero_iff_mem.mpr ha))
  have he := Finset.eq_of_subset_of_card_le hw₁ (hy w)
  exact (nonzeroAt_iff y.val m).mp (he ▸ hw₂) hyI

private def unitAction (σ : RingAut S) : Sˣ →* Sˣ := Units.map σ.toRingHom.toMonoidHom

private def unitProduct (σ : RingAut S) (l : ℕ) : Sˣ →* Sˣ :=
  ∏ i : Fin l, unitAction (σ ^ (i : ℕ))

private theorem unitProduct_val (σ : RingAut S) (l : ℕ) (x : Sˣ) :
    (unitProduct σ l x : S) = ∏ i : Fin l, (σ ^ (i : ℕ)) (x : S) := by
  rw [unitProduct, MonoidHom.finsetProd_apply]
  change (Units.coeHom S) (∏ i : Fin l, unitAction (σ ^ (i : ℕ)) x) = _
  rw [map_prod]
  rfl

/-- In a finite commutative ring with a periodic automorphism, every fixed unit
is a product of `l` consecutive conjugates of a unit, provided a scalar has
pairwise unit differences between its `l` conjugates. -/
theorem exists_prod_ringAut_eq_of_fixed [Finite S] (σ : RingAut S) {l : ℕ}
    (hl : 0 < l) (hσ : σ ^ l = 1) (a : S)
    (ha : Pairwise fun i j : Fin l => IsUnit ((σ ^ (i : ℕ)) a - (σ ^ (j : ℕ)) a))
    (y : Sˣ) (hy : σ (y : S) = y) : ∃ x : Sˣ, (∏ i : Fin l, (σ ^ (i : ℕ)) (x : S)) = y := by
  let : Finite Sˣ := Finite.of_injective (Units.val : Sˣ → S) Units.val_injective
  let d : Sˣ →* Sˣ := MonoidHom.id _ / unitAction σ
  let N := unitProduct σ l
  have hd (x : Sˣ) : (d x : S) * σ (x : S) = x := by
    change ((x / unitAction σ x : Sˣ) : S) * σ (x : S) = x
    change ((x / unitAction σ x * unitAction σ x : Sˣ) : S) = x
    rw [div_mul_cancel]
  have hker : N.ker = d.range := by
    ext u
    constructor
    · intro hu
      have hn : (∏ i : Fin l, (σ ^ (i : ℕ)) (u : S)) = 1 := by
        rw [← unitProduct_val, show N u = 1 from hu, Units.val_one]
      obtain ⟨x, hx⟩ := exists_cyclicUnitOperator_fixed_unit σ hl hσ a ha u hn
      refine ⟨x, Units.ext ?_⟩
      exact (x.isUnit.map σ.toRingHom).mul_right_cancel ((hd x).trans hx.symm)
    · rintro ⟨x, rfl⟩
      have hp : N (unitAction σ x) = N x := by
        apply Units.ext
        simp only [N, unitProduct_val]
        change (∏ i : Fin l, (σ ^ (i : ℕ)) (σ (x : S))) = _
        rw [← ringAut_prod_powers_fixed σ hσ (x : S), map_prod]
        apply Finset.prod_congr rfl
        intro i _
        change ((σ ^ (i : ℕ)) * σ) (x : S) = (σ * σ ^ (i : ℕ)) (x : S)
        rw [← pow_succ, ← pow_succ']
      change N (x / unitAction σ x) = 1
      rw [map_div, hp, div_self']
  have hle : N.range ≤ d.ker := by
    rintro _ ⟨x, rfl⟩
    have hfix : unitAction σ (N x) = N x := by
      apply Units.ext
      change σ ((N x : Sˣ) : S) = _
      simp only [N, unitProduct_val, ringAut_prod_powers_fixed σ hσ]
    change N x / unitAction σ (N x) = 1
    rw [hfix, div_self']
  have hcardN := N.ker.card_mul_index
  have hcardd := d.ker.card_mul_index
  rw [Subgroup.index_ker, hker] at hcardN
  rw [Subgroup.index_ker, mul_comm] at hcardd
  have hcard : Nat.card N.range = Nat.card d.ker :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcardN.trans hcardd.symm)
  have he : N.range = d.ker := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hmem : y ∈ d.ker := by
    have hy' : unitAction σ y = y := Units.ext hy
    change y / unitAction σ y = 1
    rw [hy', div_self']
  obtain ⟨x, hx⟩ := show y ∈ N.range from he.symm ▸ hmem
  exact ⟨x, (unitProduct_val σ l x).symm.trans (congrArg Units.val hx)⟩

end Langlands
