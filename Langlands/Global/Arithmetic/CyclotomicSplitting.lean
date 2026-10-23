import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.Arithmetic.CyclotomicAuxiliary

/-! # Cyclic cyclotomic extensions with large local degrees -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter IntermediateField
open Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped NumberField

namespace Langlands.Global.CyclotomicSplitting

universe u

section Divisibility

/-- If `ℓ ^ (A + c)` divides `X * B` with `0 < B < ℓ ^ c`, then `ℓ ^ A` divides `X`. -/
theorem pow_dvd_of_pow_add_dvd_mul {ℓ A c X B : ℕ} (hℓ : ℓ.Prime) (hB : 0 < B)
    (hBc : B < ℓ ^ c) (h : ℓ ^ (A + c) ∣ X * B) : ℓ ^ A ∣ X := by
  obtain ⟨b, B', hB', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hB.ne' ℓ hℓ.ne_one
  have hB'0 : 0 < B' := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hB
  have hb : b < c := by
    by_contra hbc
    have h1 : ℓ ^ c ≤ ℓ ^ b := Nat.pow_le_pow_right hℓ.pos (by omega)
    have h2 : ℓ ^ b ≤ ℓ ^ b * B' := Nat.le_mul_of_pos_right _ hB'0
    omega
  have hcop : Nat.Coprime (ℓ ^ (A + c)) B' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hB')
  rw [← mul_assoc] at h
  have h3 : ℓ ^ (A + c) ∣ X * ℓ ^ b := hcop.dvd_of_dvd_mul_right h
  have h4 : ℓ ^ A * ℓ ^ b ∣ X * ℓ ^ b :=
    (pow_add ℓ A b ▸ pow_dvd_pow ℓ (by omega : A + b ≤ A + c)).trans h3
  exact Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos b) h4

/-- The `ℓ`-part of the multiplicative order of a prime `p ≠ ℓ` modulo `ℓ ^ k` is unbounded:
eventually `ℓ ^ A` divides it. -/
theorem eventually_pow_dvd_orderOf {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (A : ℕ) : ∀ᶠ k in atTop, ℓ ^ A ∣ orderOf (p : ZMod (ℓ ^ k)) := by
  set N := ℓ ^ A * (ℓ - 1)
  filter_upwards [eventually_gt_atTop (p ^ N), eventually_gt_atTop 0] with k hk hk0
  by_contra hdvd
  have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hcop : Nat.Coprime p (ℓ ^ k) := ((Nat.coprime_primes hp hℓ).2 hpℓ).pow_right k
  have hφ : (p : ZMod (ℓ ^ k)) ^ Nat.totient (ℓ ^ k) = 1 := by
    have := ZMod.pow_totient (ZMod.unitOfCoprime p hcop)
    exact congrArg Units.val this
  set o := orderOf (p : ZMod (ℓ ^ k))
  have ho : o ∣ ℓ ^ (k - 1) * (ℓ - 1) := by
    rw [← Nat.totient_prime_pow hℓ hk0]
    exact orderOf_dvd_of_pow_eq_one hφ
  have ho0 : o ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at ho
    have : 0 < ℓ ^ (k - 1) * (ℓ - 1) := Nat.mul_pos (pow_pos hℓ.pos _) (by have := hℓ.two_le; omega)
    omega
  obtain ⟨b, o', ho', hoo⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 ℓ hℓ.ne_one
  have hbA : b ≤ A := by
    by_contra hb
    exact hdvd (hoo ▸ (pow_dvd_pow ℓ (by omega : A ≤ b)).trans (dvd_mul_right _ _))
  have ho'1 : o' ∣ ℓ - 1 := by
    have hcop' : Nat.Coprime o' (ℓ ^ (k - 1)) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 ho'))
    exact hcop'.dvd_of_dvd_mul_left ((Dvd.intro_left _ hoo.symm).trans ho)
  have hoN : o ∣ N := hoo ▸ mul_dvd_mul (pow_dvd_pow ℓ hbA) ho'1
  have hpN : ((p ^ N : ℕ) : ZMod (ℓ ^ k)) = ((1 : ℕ) : ZMod (ℓ ^ k)) := by
    rw [Nat.cast_pow, Nat.cast_one]
    exact orderOf_dvd_iff_pow_eq_one.1 hoN
  rw [ZMod.natCast_eq_natCast_iff'] at hpN
  have hN0 : 0 < N := Nat.mul_pos (pow_pos hℓ.pos _) (by have := hℓ.two_le; omega)
  have hpN1 : 1 < p ^ N := Nat.one_lt_pow hN0.ne' hp.one_lt
  have hdvd' : ℓ ^ k ∣ p ^ N - 1 :=
    (Nat.modEq_iff_dvd' hpN1.le).1 (show 1 ≡ p ^ N [MOD ℓ ^ k] from hpN.symm)
  have hle := Nat.le_of_dvd (by omega) hdvd'
  have hlt : k < ℓ ^ k := Nat.lt_pow_self hℓ.one_lt
  omega

end Divisibility

section Groups

/-- A group `A` receiving a surjection `f` from `G` is cyclic if some homomorphism `ψ` from `G`
to a cyclic group has kernel inside the kernel of `f`. -/
theorem isCyclic_of_ker_le {G A Q : Type*} [Group G] [Group A] [Group Q] [IsCyclic Q]
    (f : G →* A) (hf : Function.Surjective f) (ψ : G →* Q) (h : ψ.ker ≤ f.ker) :
    IsCyclic A := by
  have : IsCyclic (G ⧸ ψ.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ)
  refine isCyclic_of_surjective (QuotientGroup.lift ψ.ker f h) fun x => ?_
  obtain ⟨g, rfl⟩ := hf x
  exact ⟨(g : G ⧸ ψ.ker), rfl⟩

/-- The powers of an element of order two are `1` and the element itself. -/
theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {g x : G} (hg : orderOf g = 2)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hg, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

/-- The square of `2 ^ (i + 2) - 1` in `ZMod (2 ^ (i + 3))` is `1`. -/
theorem twoPow_sub_one_mul_self (i : ℕ) :
    ((2 : ZMod (2 ^ (i + 3))) ^ (i + 2) - 1) * ((2 : ZMod (2 ^ (i + 3))) ^ (i + 2) - 1) = 1 := by
  have h0 : (2 : ZMod (2 ^ (i + 3))) ^ (i + 3) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ (i + 3))
  linear_combination (2 ^ (i + 1) - 1 : ZMod (2 ^ (i + 3))) * h0

/-- The unit `2 ^ (i + 2) - 1` of `ZMod (2 ^ (i + 3))`: the exponent `e` with `ζ ^ e = -ζ⁻¹` for
a primitive `2 ^ (i + 3)`-th root of unity `ζ`. -/
def twoPowUnit (i : ℕ) : (ZMod (2 ^ (i + 3)))ˣ :=
  Units.mkOfMulEqOne _ _ (twoPow_sub_one_mul_self i)

theorem val_twoPowUnit (i : ℕ) :
    ((twoPowUnit i : (ZMod (2 ^ (i + 3)))ˣ) : ZMod (2 ^ (i + 3))) = 2 ^ (i + 2) - 1 :=
  rfl

theorem four_dvd_two_pow (i : ℕ) : 4 ∣ 2 ^ (i + 3) :=
  ⟨2 ^ (i + 1), by ring⟩

/-- Modulo `4`, the unit `2 ^ (i + 2) - 1` is `-1`. -/
theorem castHom_twoPowUnit (i : ℕ) :
    ZMod.castHom (four_dvd_two_pow i) (ZMod 4)
      ((twoPowUnit i : (ZMod (2 ^ (i + 3)))ˣ) : ZMod (2 ^ (i + 3))) = -1 := by
  rw [val_twoPowUnit, map_sub, map_pow, map_one, map_ofNat]
  have : (2 : ZMod 4) ^ (i + 2) = 0 := by
    rw [pow_add, show (2 : ZMod 4) ^ 2 = 0 from by decide, mul_zero]
  rw [this, zero_sub]

theorem twoPowUnit_ne_one (i : ℕ) : twoPowUnit i ≠ 1 := by
  intro h
  have := castHom_twoPowUnit i
  rw [h, Units.val_one, map_one] at this
  exact absurd this (by decide)

theorem orderOf_twoPowUnit (i : ℕ) : orderOf (twoPowUnit i) = 2 := by
  refine orderOf_eq_prime (Units.ext ?_) (twoPowUnit_ne_one i)
  rw [Units.val_pow_eq_pow_val, val_twoPowUnit, sq, twoPow_sub_one_mul_self, Units.val_one]

/-- The unit `5` of `ZMod (2 ^ (i + 3))`. -/
def fiveUnit (i : ℕ) : (ZMod (2 ^ (i + 3)))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))

theorem orderOf_fiveUnit (i : ℕ) : orderOf (fiveUnit i) = 2 ^ (i + 1) := by
  rw [← orderOf_units, fiveUnit, ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  exact ZMod.orderOf_five (i + 1)

/-- No power of `5` is `2 ^ (i + 2) - 1` modulo `2 ^ (i + 3)` (compare both modulo `4`). -/
theorem fiveUnit_pow_eq_one {i t : ℕ} (h : fiveUnit i ^ t ∈ Subgroup.zpowers (twoPowUnit i)) :
    fiveUnit i ^ t = 1 := by
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_twoPowUnit i) h with h1 | h2
  · exact h1
  · exfalso
    have h4 := castHom_twoPowUnit i
    rw [← h2, Units.val_pow_eq_pow_val, map_pow, fiveUnit, ZMod.coe_unitOfCoprime,
      map_natCast, show ((5 : ℕ) : ZMod 4) = 1 from by decide, one_pow] at h4
    exact absurd h4 (by decide)

/-- `(ZMod (2 ^ (i + 3)))ˣ ⧸ ⟨2 ^ (i + 2) - 1⟩` is cyclic, generated by the class of `5`. -/
theorem isCyclic_units_quotient_twoPowUnit (i : ℕ) :
    IsCyclic ((ZMod (2 ^ (i + 3)))ˣ ⧸ Subgroup.zpowers (twoPowUnit i)) := by
  set N := Subgroup.zpowers (twoPowUnit i)
  set q := QuotientGroup.mk' N (fiveUnit i)
  have hq : orderOf q = 2 ^ (i + 1) := by
    refine (Nat.dvd_antisymm (orderOf_map_dvd _ _)
      (orderOf_dvd_of_pow_eq_one (fiveUnit_pow_eq_one ?_))).trans (orderOf_fiveUnit i)
    have := pow_orderOf_eq_one q
    rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hcard : Nat.card ((ZMod (2 ^ (i + 3)))ˣ ⧸ N) = 2 ^ (i + 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [Nat.card_zpowers, orderOf_twoPowUnit, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)] at h1
    have h2 : 2 ^ (i + 3 - 1) * (2 - 1) = 2 ^ (i + 1) * 2 := by
      rw [show i + 3 - 1 = i + 1 + 1 from rfl, pow_succ, show (2 : ℕ) - 1 = 1 from rfl, mul_one]
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  exact isCyclic_of_orderOf_eq_card q (hq.trans hcard.symm)

end Groups

section Construction

variable (F : Type u) [Field F] [NumberField F] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (k : ℕ)

instance neZero_pow : NeZero (ℓ ^ (k + 3)) :=
  ⟨pow_ne_zero _ hℓ.out.ne_zero⟩

/-- The cyclotomic layer `F(ζ)`, for `ζ` a primitive `ℓ ^ (k + 3)`-th root of unity. -/
abbrev Layer : Type u :=
  CyclotomicField (ℓ ^ (k + 3)) F

/-- The chosen primitive `ℓ ^ (k + 3)`-th root of unity in the layer. -/
abbrev zeta : Layer F ℓ k :=
  IsCyclotomicExtension.zeta (ℓ ^ (k + 3)) F (Layer F ℓ k)

theorem zeta_spec : IsPrimitiveRoot (zeta F ℓ k) (ℓ ^ (k + 3)) :=
  IsCyclotomicExtension.zeta_spec _ _ _

theorem zeta_ne_zero : zeta F ℓ k ≠ 0 :=
  (zeta_spec F ℓ k).ne_zero (NeZero.ne _)

instance isGalois_layer : IsGalois F (Layer F ℓ k) :=
  IsCyclotomicExtension.isGalois {ℓ ^ (k + 3)} F _

/-- The element `ξ = ζ - ζ⁻¹` of the layer. -/
def xi : Layer F ℓ k :=
  zeta F ℓ k - (zeta F ℓ k)⁻¹

/-- The automorphisms of the layer over `F` fixing `ξ`. -/
def xiStabilizer : Subgroup (Layer F ℓ k ≃ₐ[F] Layer F ℓ k) :=
  MulAction.stabilizer _ (xi F ℓ k)

/-- The fixed field of the stabilizer of `ξ`; by the Galois correspondence it is `F(ξ)`. -/
def xiField : IntermediateField F (Layer F ℓ k) :=
  IntermediateField.fixedField (xiStabilizer F ℓ k)

instance numberField_xiField : NumberField (xiField F ℓ k) :=
  intermediateField_numberField _

instance normal_xiStabilizer : (xiStabilizer F ℓ k).Normal := by
  have := IsCyclotomicExtension.isMulCommutative {ℓ ^ (k + 3)} F (Layer F ℓ k)
  exact Subgroup.normal_of_isMulCommutative _

instance isGalois_xiField : IsGalois F (xiField F ℓ k) :=
  IsGalois.of_fixedField_normal_subgroup _

variable {F ℓ k}

/-- An automorphism of the layer is determined by its value at `ζ`. -/
theorem algEquiv_ext_of_apply_zeta {σ τ : Layer F ℓ k ≃ₐ[F] Layer F ℓ k}
    (h : σ (zeta F ℓ k) = τ (zeta F ℓ k)) : σ = τ := by
  refine AlgEquiv.coe_toAlgHom_injective (((zeta_spec F ℓ k).powerBasis F).algHom_ext ?_)
  rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, IsPrimitiveRoot.powerBasis_gen]
  exact h

theorem apply_xi (σ : Layer F ℓ k ≃ₐ[F] Layer F ℓ k) :
    σ (xi F ℓ k) = σ (zeta F ℓ k) - (σ (zeta F ℓ k))⁻¹ := by
  rw [xi, map_sub, map_inv₀]

/-- An automorphism fixing `ξ` sends `ζ` to `ζ` or to `-ζ⁻¹`. -/
theorem apply_zeta_of_mem {σ : Layer F ℓ k ≃ₐ[F] Layer F ℓ k} (hσ : σ ∈ xiStabilizer F ℓ k) :
    σ (zeta F ℓ k) = zeta F ℓ k ∨ σ (zeta F ℓ k) = -(zeta F ℓ k)⁻¹ := by
  have h : σ (xi F ℓ k) = xi F ℓ k := hσ
  rw [apply_xi, xi] at h
  set x := σ (zeta F ℓ k)
  set z := zeta F ℓ k
  have hz : z * z⁻¹ = 1 := mul_inv_cancel₀ (zeta_ne_zero F ℓ k)
  have hx : x * x⁻¹ = 1 := mul_inv_cancel₀ ((map_ne_zero σ).2 (zeta_ne_zero F ℓ k))
  have h0 : (x - z) * (x + z⁻¹) = 0 := by linear_combination x * h + hx - hz
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- An automorphism sending `ζ` to `-ζ⁻¹` fixes `ξ`. -/
theorem mem_of_apply_zeta {σ : Layer F ℓ k ≃ₐ[F] Layer F ℓ k}
    (hσ : σ (zeta F ℓ k) = -(zeta F ℓ k)⁻¹) : σ ∈ xiStabilizer F ℓ k := by
  change σ (xi F ℓ k) = xi F ℓ k
  rw [apply_xi, hσ, inv_neg, inv_inv, xi]
  ring

variable (F ℓ k)

theorem card_xiStabilizer_le : Nat.card (xiStabilizer F ℓ k) ≤ 2 := by
  classical
  let f : xiStabilizer F ℓ k → ({zeta F ℓ k, -(zeta F ℓ k)⁻¹} : Set (Layer F ℓ k)) :=
    fun σ => ⟨(σ : Layer F ℓ k ≃ₐ[F] Layer F ℓ k) (zeta F ℓ k), apply_zeta_of_mem σ.2⟩
  have hf : Function.Injective f := fun σ τ h =>
    Subtype.ext (algEquiv_ext_of_apply_zeta (congrArg Subtype.val h))
  calc Nat.card (xiStabilizer F ℓ k)
      ≤ Nat.card ({zeta F ℓ k, -(zeta F ℓ k)⁻¹} : Set (Layer F ℓ k)) :=
        Nat.card_le_card_of_injective f hf
    _ = Set.ncard ({zeta F ℓ k, -(zeta F ℓ k)⁻¹} : Set (Layer F ℓ k)) :=
        Nat.card_coe_set_eq _
    _ ≤ Set.ncard ({-(zeta F ℓ k)⁻¹} : Set (Layer F ℓ k)) + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- The layer has degree at most `2` over `xiField`. -/
theorem finrank_layer_le : Module.finrank (xiField F ℓ k) (Layer F ℓ k) ≤ 2 := by
  rw [xiField, IntermediateField.finrank_fixedField_eq_card]
  exact card_xiStabilizer_le F ℓ k

instance isGalois_layer_xiField : IsGalois (xiField F ℓ k) (Layer F ℓ k) :=
  IsGalois.tower_top_of_isGalois F (xiField F ℓ k) (Layer F ℓ k)

theorem restrictNormalHom_eq_one {σ : Layer F ℓ k ≃ₐ[F] Layer F ℓ k}
    (hσ : σ ∈ xiStabilizer F ℓ k) : AlgEquiv.restrictNormalHom (xiField F ℓ k) σ = 1 := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
  exact (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ hσ

/-- For `ℓ = 2`, the automorphism with exponent `2 ^ (k + 2) - 1` sends `ζ` to `-ζ⁻¹`. -/
theorem apply_zeta_of_autToPow_eq_twoPowUnit (F : Type u) [Field F] [NumberField F] (k : ℕ)
    [Fact (Nat.Prime 2)] (σ : Layer F 2 k ≃ₐ[F] Layer F 2 k)
    (hσ : (zeta_spec F 2 k).autToPow F σ = twoPowUnit k) :
    σ (zeta F 2 k) = -(zeta F 2 k)⁻¹ := by
  have hz := zeta_spec F 2 k
  rw [← hz.autToPow_spec F σ, hσ, val_twoPowUnit]
  have hlt : 2 ^ (k + 2) - 1 < 2 ^ (k + 3) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hcast : ((2 : ZMod (2 ^ (k + 3))) ^ (k + 2) - 1) = ((2 ^ (k + 2) - 1 : ℕ) : ZMod _) := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, pow_sub₀ _ (zeta_ne_zero F 2 k)
    Nat.one_le_two_pow, pow_one]
  have h2 : IsPrimitiveRoot (zeta F 2 k ^ 2 ^ (k + 2)) 2 :=
    hz.pow (pow_pos two_pos _) (by ring)
  rw [h2.eq_neg_one_of_two_right, neg_one_mul]

/-- The Galois group of `xiField` over `F` is cyclic. -/
theorem isCyclic_xiField : IsCyclic (xiField F ℓ k ≃ₐ[F] xiField F ℓ k) := by
  have hζ := zeta_spec F ℓ k
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := xiField F ℓ k)
    (Layer F ℓ k)
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have := isCyclic_units_quotient_twoPowUnit k
    refine isCyclic_of_ker_le _ hsurj ((QuotientGroup.mk' (Subgroup.zpowers (twoPowUnit k))).comp
      (hζ.autToPow F)) fun σ hσ => ?_
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hσ
    rw [MonoidHom.mem_ker]
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_twoPowUnit k) hσ with h1 | h1
    · rw [hζ.autToPow_injective F (h1.trans (map_one _).symm), map_one]
    · exact restrictNormalHom_eq_one F 2 k
        (mem_of_apply_zeta (apply_zeta_of_autToPow_eq_twoPowUnit F k σ h1))
  · have := ZMod.isCyclic_units_of_prime_pow ℓ hℓ.out hℓ2 (k + 3)
    refine isCyclic_of_ker_le _ hsurj (hζ.autToPow F) ?_
    rw [(MonoidHom.ker_eq_bot_iff _).2 (hζ.autToPow_injective F)]
    exact bot_le

/-- Every infinite place of `xiField` is complex: `ξ = ζ - ζ⁻¹` is never real. -/
theorem isComplex_xiField (w : InfinitePlace (xiField F ℓ k)) : w.IsComplex := by
  rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
  intro hw
  set φ := w.embedding
  set ψ := ComplexEmbedding.lift (Layer F ℓ k) φ
  have hξ : xi F ℓ k ∈ xiField F ℓ k :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hσ
  have h1 : φ ⟨xi F ℓ k, hξ⟩ = ψ (zeta F ℓ k) - (ψ (zeta F ℓ k))⁻¹ := by
    rw [← ComplexEmbedding.lift_algebraMap_apply (Layer F ℓ k) φ, ← map_inv₀, ← map_sub]
    rfl
  have hz : IsPrimitiveRoot (ψ (zeta F ℓ k)) (ℓ ^ (k + 3)) :=
    (zeta_spec F ℓ k).map_of_injective ψ.injective
  set z := ψ (zeta F ℓ k)
  have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one (NeZero.ne _)
  have hconj : z⁻¹ = (starRingEnd ℂ) z := Complex.inv_eq_conj hnorm
  have h2 := congrArg (fun f : xiField F ℓ k →+* ℂ => f ⟨xi F ℓ k, hξ⟩) hw
  simp only [ComplexEmbedding.conjugate_coe_eq] at h2
  rw [h1, hconj, map_sub, Complex.conj_conj] at h2
  have h3 : z = (starRingEnd ℂ) z := by linear_combination (-1 / 2 : ℂ) * h2
  have h4 : z ^ 2 = 1 := by
    rw [sq]
    nth_rw 2 [h3]
    rw [← hconj, mul_inv_cancel₀ (hz.ne_zero (NeZero.ne _))]
  have h5 := hz.dvd_of_pow_eq_one 2 h4
  have h6 : 8 ≤ ℓ ^ (k + 3) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ ℓ ^ 3 := Nat.pow_le_pow_left hℓ.out.two_le 3
      _ ≤ ℓ ^ (k + 3) := Nat.pow_le_pow_right hℓ.out.pos (by omega)
  have := Nat.le_of_dvd two_pos h5
  omega

end Construction

section LocalDegrees

/-- In a cyclotomic field `ℚ(ζ)` with `ζ` of order `ℓ ^ (k + 3)`, `ℓ ^ A` divides the product of
ramification index and inertia degree over `ℤ` of a prime above `p`, provided `A ≤ k + 2` when
`p = ℓ` and `ℓ ^ A` divides the order of `p` modulo `ℓ ^ (k + 3)` when `p ≠ ℓ`. -/
theorem pow_dvd_ramificationIdx_mul_inertiaDeg {ℓ k A : ℕ} [hℓ : Fact ℓ.Prime] (p : ℕ)
    [hp : Fact p.Prime] {Z : Type*} [Field Z] [NumberField Z]
    [IsCyclotomicExtension {ℓ ^ (k + 3)} ℚ Z] (P : Ideal (𝓞 Z)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (h1 : p = ℓ → A ≤ k + 2)
    (h2 : p ≠ ℓ → ℓ ^ A ∣ orderOf (p : ZMod (ℓ ^ (k + 3)))) :
    ℓ ^ A ∣ P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    have : IsCyclotomicExtension {p ^ (k + 2 + 1)} ℚ Z :=
      ‹IsCyclotomicExtension {p ^ (k + 3)} ℚ Z›
    rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow p (k + 2) Z P,
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow p (k + 2) Z P, mul_one]
    exact (pow_dvd_pow p (h1 rfl)).mul_right _
  · have hm : ¬ p ∣ ℓ ^ (k + 3) := fun h =>
      hpℓ ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 (hp.out.dvd_of_dvd_pow h))
    rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p Z P hm,
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p Z P hm, one_mul]
    exact h2 hpℓ

/-- The product of ramification index and inertia degree over `ℤ` of a prime of a number field
is at most the degree of the field. -/
theorem ramificationIdx_mul_inertiaDeg_le_finrank {K : Type*} [Field K] [NumberField K] (p : ℕ)
    [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ * P.inertiaDeg ℤ ≤ Module.finrank ℚ K := by
  classical
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank] at h
  rw [← h]
  exact Finset.single_le_sum
    (f := fun Q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) =>
      Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨P, ‹_›, ‹_›⟩)

variable (F : Type u) [Field F] [NumberField F] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (k : ℕ)

/-- The local degree of `xiField` at a place above `v` is divisible by `ℓ ^ a` as soon as, for the
residue characteristic `p` of `v` and `A = a + 2 + [F : ℚ]`, either `p = ℓ` and `A ≤ k + 2`, or
`p ≠ ℓ` and `ℓ ^ A` divides the order of `p` modulo `ℓ ^ (k + 3)`. -/
theorem pow_dvd_localDegree (a : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h1 : Ideal.absNorm (v.asIdeal.under ℤ) = ℓ → a + 2 + Module.finrank ℚ F ≤ k + 2)
    (h2 : Ideal.absNorm (v.asIdeal.under ℤ) ≠ ℓ → ℓ ^ (a + 2 + Module.finrank ℚ F) ∣
      orderOf ((Ideal.absNorm (v.asIdeal.under ℤ) : ℕ) : ZMod (ℓ ^ (k + 3))))
    (w : HeightOneSpectrum (𝓞 (xiField F ℓ k))) [w.asIdeal.LiesOver v.asIdeal] :
    ℓ ^ a ∣ Module.finrank (v.adicCompletion F) (w.adicCompletion (xiField F ℓ k)) := by
  classical
  set d := Module.finrank ℚ F
  set p := Ideal.absNorm (v.asIdeal.under ℤ)
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime v.asIdeal⟩
  let u := (placeAbove (Layer F ℓ k) w).1
  have hu : u.asIdeal.LiesOver w.asIdeal := (placeAbove (Layer F ℓ k) w).2
  have huv : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  have hup : u.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans u.asIdeal v.asIdeal _
  have hζ := zeta_spec F ℓ k
  have : IsCyclotomicExtension {ℓ ^ (k + 3)} ℚ ℚ⟮zeta F ℓ k⟯ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let P₀ : Ideal (𝓞 ℚ⟮zeta F ℓ k⟯) := u.asIdeal.under (𝓞 ℚ⟮zeta F ℓ k⟯)
  have : u.asIdeal.LiesOver P₀ := ⟨rfl⟩
  have : P₀.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.tower_bot u.asIdeal P₀ _
  have hZ : ℓ ^ (a + 2 + d) ∣ P₀.ramificationIdx ℤ * P₀.inertiaDeg ℤ :=
    pow_dvd_ramificationIdx_mul_inertiaDeg p P₀ h1 h2
  have hZu : u.asIdeal.ramificationIdx ℤ * u.asIdeal.inertiaDeg ℤ =
      (P₀.ramificationIdx ℤ * P₀.inertiaDeg ℤ) *
        (u.asIdeal.ramificationIdx (𝓞 ℚ⟮zeta F ℓ k⟯) *
          u.asIdeal.inertiaDeg (𝓞 ℚ⟮zeta F ℓ k⟯)) := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) P₀ u.asIdeal,
      Ideal.inertiaDeg_tower (R := ℤ) P₀ u.asIdeal]
    ring
  have hvu : u.asIdeal.ramificationIdx ℤ * u.asIdeal.inertiaDeg ℤ =
      (u.asIdeal.ramificationIdx (𝓞 F) * u.asIdeal.inertiaDeg (𝓞 F)) *
        (v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ) := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal u.asIdeal,
      Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal u.asIdeal]
    ring
  have hwu : u.asIdeal.ramificationIdx (𝓞 F) * u.asIdeal.inertiaDeg (𝓞 F) =
      (w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F)) *
        (u.asIdeal.ramificationIdx (𝓞 (xiField F ℓ k)) * u.asIdeal.inertiaDeg (𝓞 (xiField F ℓ k))) := by
    rw [Ideal.ramificationIdx_tower (R := 𝓞 F) w.asIdeal u.asIdeal,
      Ideal.inertiaDeg_tower (R := 𝓞 F) w.asIdeal u.asIdeal]
    ring
  have hB1 : 0 < v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ :=
    Nat.mul_pos (Ideal.ramificationIdx_pos _ ℤ) (Ideal.inertiaDeg_pos _ ℤ)
  have hB1' : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ < ℓ ^ d :=
    lt_of_le_of_lt (ramificationIdx_mul_inertiaDeg_le_finrank p v.asIdeal)
      (Nat.lt_pow_self hℓ.out.one_lt)
  have hB2 : 0 < u.asIdeal.ramificationIdx (𝓞 (xiField F ℓ k)) * u.asIdeal.inertiaDeg (𝓞 (xiField F ℓ k)) :=
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hB2' : u.asIdeal.ramificationIdx (𝓞 (xiField F ℓ k)) * u.asIdeal.inertiaDeg (𝓞 (xiField F ℓ k)) < ℓ ^ 2 := by
    have h := localDegree_dvd w u
    rw [localDegree_eq w u] at h
    have h3 := Nat.le_of_dvd Module.finrank_pos h
    have h4 := finrank_layer_le F ℓ k
    have h5 : 4 ≤ ℓ ^ 2 := by
      have := hℓ.out.two_le
      nlinarith
    omega
  have h3 : ℓ ^ (a + 2 + d) ∣
      (u.asIdeal.ramificationIdx (𝓞 F) * u.asIdeal.inertiaDeg (𝓞 F)) *
        (v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ) :=
    hvu ▸ hZu ▸ hZ.mul_right _
  have h4 := pow_dvd_of_pow_add_dvd_mul hℓ.out hB1 hB1' h3
  rw [hwu] at h4
  rw [localDegree_eq v w]
  exact pow_dvd_of_pow_add_dvd_mul hℓ.out hB2 hB2' h4

/-- For every finite set `S` of finite places of `F`, there is `k` such that all local degrees
of `xiField F ℓ k` over the places in `S` are divisible by `ℓ ^ a`. -/
theorem exists_pow_dvd_localDegree (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ k : ℕ, ∀ v ∈ S, ∀ (w : HeightOneSpectrum (𝓞 (xiField F ℓ k)))
      [w.asIdeal.LiesOver v.asIdeal],
        ℓ ^ a ∣ Module.finrank (v.adicCompletion F) (w.adicCompletion (xiField F ℓ k)) := by
  classical
  set A := a + 2 + Module.finrank ℚ F
  have hev : ∀ v ∈ S, ∀ᶠ k in atTop,
      (Ideal.absNorm (v.asIdeal.under ℤ) = ℓ → A ≤ k + 2) ∧
        (Ideal.absNorm (v.asIdeal.under ℤ) ≠ ℓ → ℓ ^ A ∣
          orderOf ((Ideal.absNorm (v.asIdeal.under ℤ) : ℕ) : ZMod (ℓ ^ (k + 3)))) := by
    intro v _
    have : NeZero v.asIdeal := ⟨v.ne_bot⟩
    have hp := Nat.absNorm_under_prime v.asIdeal
    by_cases hpℓ : Ideal.absNorm (v.asIdeal.under ℤ) = ℓ
    · filter_upwards [eventually_ge_atTop A] with k hk
      exact ⟨fun _ => by omega, fun h => absurd hpℓ h⟩
    · filter_upwards [(tendsto_add_atTop_nat 3).eventually
        (eventually_pow_dvd_orderOf hℓ.out hp hpℓ A)] with k hk
      exact ⟨fun h => absurd h hpℓ, fun _ => hk⟩
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finset S).2 hev).exists
  refine ⟨k, ?_⟩
  intro v hv w _
  exact pow_dvd_localDegree F ℓ k a v (hk v hv).1 (hk v hv).2 w

/-- **Cyclic cyclotomic splitting.** For a number field `F`, a prime `ℓ`, `a : ℕ` and a finite
set `S` of finite places of `F`, there is a cyclic Galois extension `K / F` contained in a
cyclotomic extension of `F`, all of whose infinite places are complex, whose local degrees at
the places above `S` are all divisible by `ℓ ^ a`. -/
theorem exists_cyclic_splitting (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (K : Type u) (_ : Field K) (_ : NumberField K) (_ : Algebra F K), IsGalois F K ∧
      IsCyclic (K ≃ₐ[F] K) ∧ (∃ m : ℕ, 0 < m ∧ Nonempty (K →ₐ[F] CyclotomicField m F)) ∧
      (∀ v ∈ S, ∀ (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal],
        ℓ ^ a ∣ Module.finrank (v.adicCompletion F) (w.adicCompletion K)) ∧
      ∀ w : InfinitePlace K, w.IsComplex := by
  obtain ⟨k, hk⟩ := exists_pow_dvd_localDegree F ℓ a S
  exact ⟨xiField F ℓ k, inferInstance, inferInstance, inferInstance, inferInstance,
    isCyclic_xiField F ℓ k, ⟨ℓ ^ (k + 3), pow_pos hℓ.out.pos _, ⟨(xiField F ℓ k).val⟩⟩, hk,
    isComplex_xiField F ℓ k⟩

end LocalDegrees

end Langlands.Global.CyclotomicSplitting
