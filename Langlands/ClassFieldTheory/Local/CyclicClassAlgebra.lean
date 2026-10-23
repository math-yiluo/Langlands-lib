import Langlands.ClassFieldTheory.Local.UnramifiedInvariantInflationProof

/-! # Algebra of cyclic carry classes

Additivity of `cyclicClass K L χ a` in the unit `a` and in the character `χ`, independence
of the modulus under scaling, naturality under maps of group cohomology, and the norm
criterion for its vanishing.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v w

namespace CyclicClassAlgebra

section Basic

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]

theorem baseUnit_mul (a b : Kˣ) :
    baseUnit K L (a * b) = baseUnit K L a + baseUnit K L b := by
  change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom (a * b)) =
    Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a) +
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom b)
  rw [map_mul]
  rfl

theorem baseUnit_one : baseUnit K L 1 = 0 := by
  change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom 1) = 0
  rw [map_one]
  rfl

variable {K L} {n : ℕ} [NeZero n]

theorem cyclicUnitCocycle_apply (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ)
    (g h : Gal(L/K)) :
    cyclicUnitCocycle K L χ a (g, h) = cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L a :=
  rfl

/-- The carry class is additive in the unit. -/
theorem cyclicClass_mul (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a b : Kˣ) :
    cyclicClass K L χ (a * b) = cyclicClass K L χ a + cyclicClass K L χ b := by
  rw [cyclicClass, cyclicClass, cyclicClass, ← map_add]
  congr 1
  refine groupCohomology.cocycles₂_ext fun g h => ?_
  change cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L (a * b) =
    cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L a +
      cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L b
  rw [baseUnit_mul, nsmul_add]

theorem cyclicClass_one (χ : Gal(L/K) →* Multiplicative (ZMod n)) :
    cyclicClass K L χ 1 = 0 := by
  have h := cyclicClass_mul χ (1 : Kˣ) 1
  rw [mul_one] at h
  exact left_eq_add.1 h

/-- The carry class as an additive map in the unit. -/
def cyclicClassHom (χ : Gal(L/K) →* Multiplicative (ZMod n)) :
    Additive Kˣ →+ relativeCohomology K L 2 where
  toFun a := cyclicClass K L χ (Additive.toMul a)
  map_zero' := cyclicClass_one χ
  map_add' a b := cyclicClass_mul χ (Additive.toMul a) (Additive.toMul b)

theorem cyclicClassHom_apply (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    cyclicClassHom χ (Additive.ofMul a) = cyclicClass K L χ a :=
  rfl

theorem cyclicClass_pow (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) (k : ℕ) :
    cyclicClass K L χ (a ^ k) = k • cyclicClass K L χ a := by
  rw [← cyclicClassHom_apply, ofMul_pow, map_nsmul, cyclicClassHom_apply]

theorem cyclicClass_inv (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    cyclicClass K L χ a⁻¹ = -cyclicClass K L χ a := by
  rw [← cyclicClassHom_apply, ofMul_inv, map_neg, cyclicClassHom_apply]

/-- The carries of a product of characters, corrected by the carries of the sums. -/
theorem carry_mul_identity (x₁ x₂ y₁ y₂ : ZMod n) :
    cyclicCarry (x₁ + x₂) (y₁ + y₂) + cyclicCarry x₁ x₂ + cyclicCarry y₁ y₂ =
      cyclicCarry x₁ y₁ + cyclicCarry x₂ y₂ + cyclicCarry (x₁ + y₁) (x₂ + y₂) := by
  have h₁ := cyclicCarry_spec (x₁ + x₂) (y₁ + y₂)
  have h₂ := cyclicCarry_spec x₁ x₂
  have h₃ := cyclicCarry_spec y₁ y₂
  have h₄ := cyclicCarry_spec x₁ y₁
  have h₅ := cyclicCarry_spec x₂ y₂
  have h₆ := cyclicCarry_spec (x₁ + y₁) (x₂ + y₂)
  have hs : x₁ + y₁ + (x₂ + y₂) = x₁ + x₂ + (y₁ + y₂) := by abel
  rw [hs] at h₆
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  rw [mul_add, mul_add, mul_add, mul_add]
  omega

/-- The carry class is additive in the character. -/
theorem cyclicClass_mul_character (χ₁ χ₂ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    cyclicClass K L (χ₁ * χ₂) a = cyclicClass K L χ₁ a + cyclicClass K L χ₂ a := by
  rw [cyclicClass, cyclicClass, cyclicClass, ← map_add, groupCohomology.H2π_eq_iff]
  refine ⟨fun g => -((cyclicCarry (χ₁ g).toAdd (χ₂ g).toAdd : ℤ) • baseUnit K L a), ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have hid := carry_mul_identity (χ₁ g).toAdd (χ₂ g).toAdd (χ₁ h).toAdd (χ₂ h).toAdd
  rw [groupCohomology.d₁₂_hom_apply]
  change (unitsRepresentation K L).ρ g
        (-((cyclicCarry (χ₁ h).toAdd (χ₂ h).toAdd : ℤ) • baseUnit K L a)) -
      -((cyclicCarry (χ₁ (g * h)).toAdd (χ₂ (g * h)).toAdd : ℤ) • baseUnit K L a) +
      -((cyclicCarry (χ₁ g).toAdd (χ₂ g).toAdd : ℤ) • baseUnit K L a) =
    cyclicCarry ((χ₁ * χ₂) g).toAdd ((χ₁ * χ₂) h).toAdd • baseUnit K L a -
      (cyclicCarry (χ₁ g).toAdd (χ₁ h).toAdd • baseUnit K L a +
        cyclicCarry (χ₂ g).toAdd (χ₂ h).toAdd • baseUnit K L a)
  rw [map_neg, map_zsmul, baseUnit_fixed]
  simp only [MonoidHom.mul_apply, map_mul, toAdd_mul] at hid ⊢
  simp only [← natCast_zsmul, ← neg_smul, ← sub_smul, ← add_smul]
  congr 1
  have hz := congrArg (fun m : ℕ => (m : ℤ)) hid
  push_cast at hz
  linarith

theorem cyclicClass_one_character (a : Kˣ) :
    cyclicClass K L (1 : Gal(L/K) →* Multiplicative (ZMod n)) a = 0 := by
  have h := cyclicClass_mul_character (1 : Gal(L/K) →* Multiplicative (ZMod n)) 1 a
  rw [mul_one] at h
  exact left_eq_add.1 h

theorem cyclicClass_pow_character (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ)
    (k : ℕ) : cyclicClass K L (χ ^ k) a = k • cyclicClass K L χ a := by
  induction k with
  | zero => rw [pow_zero, cyclicClass_one_character, zero_smul]
  | succ k ih => rw [pow_succ, cyclicClass_mul_character, ih, succ_nsmul]

theorem cyclicClass_inv_character (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    cyclicClass K L χ⁻¹ a = -cyclicClass K L χ a := by
  have h := cyclicClass_mul_character χ⁻¹ χ a
  rw [inv_mul_cancel, cyclicClass_one_character] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Carry classes for two moduli agree when the standard representatives are proportional:
for `n = e * k`, a character `ψ` into `ℤ/n` with representatives `k` times those of a
character `χ` into `ℤ/e` has the same carries, hence the same class. -/
theorem cyclicClass_eq_of_val_eq {e k : ℕ} [NeZero e] (hn : n = e * k)
    (ψ : Gal(L/K) →* Multiplicative (ZMod n)) (χ : Gal(L/K) →* Multiplicative (ZMod e))
    (hval : ∀ g, (ψ g).toAdd.val = k * (χ g).toAdd.val) (a : Kˣ) :
    cyclicClass K L ψ a = cyclicClass K L χ a := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (by rw [hn, h, mul_zero]) (NeZero.ne n)
    · exact h
  rw [cyclicClass, cyclicClass]
  congr 1
  refine groupCohomology.cocycles₂_ext fun g h => ?_
  rw [cyclicUnitCocycle_apply, cyclicUnitCocycle_apply]
  congr 1
  rw [cyclicCarry, cyclicCarry, hval, hval, hn, ← mul_add, mul_comm e k,
    Nat.mul_div_mul_left _ _ hk]

end Basic

section Naturality

variable {K : Type v} {L : Type u} [Field K] [Field L] [Algebra K L]
  {K' : Type w} {L' : Type u} [Field K'] [Field L'] [Algebra K' L'] {n : ℕ} [NeZero n]

/-- A map of group cohomology along a group homomorphism and a coefficient map sending the
base unit `a` to the base unit `a'` sends the carry class of `a` to the carry class of `a'`
for the pulled-back character. -/
theorem map_cyclicClass (φ : Gal(L'/K') →* Gal(L/K))
    (f : Rep.res φ (unitsRepresentation K L) ⟶ unitsRepresentation K' L')
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) (a' : K'ˣ)
    (hf : f.hom (baseUnit K L a) = baseUnit K' L' a') :
    groupCohomology.map φ f 2 (cyclicClass K L χ a) = cyclicClass K' L' (χ.comp φ) a' := by
  rw [cyclicClass, cyclicClass, groupCohomology.H2π_comp_map_apply]
  congr 1
  refine groupCohomology.cocycles₂_ext fun g h => ?_
  change f.hom (cyclicCarry (χ (φ g)).toAdd (χ (φ h)).toAdd • baseUnit K L a) =
    cyclicCarry (χ (φ g)).toAdd (χ (φ h)).toAdd • baseUnit K' L' a'
  rw [map_nsmul, hf]

end Naturality

section Norm

/-- An injective character of a finite group into `ℤ/n` is a scaled isomorphism onto
`ℤ/|G|`: `n = |G| · k` and its standard representatives are `k` times those of a group
isomorphism `G ≃ ℤ/|G|`. -/
theorem exists_mulEquiv_of_injective {G : Type*} [Group G] [Finite G] {n : ℕ} [NeZero n]
    (ψ : G →* Multiplicative (ZMod n)) (hψ : Function.Injective ψ) :
    ∃ k : ℕ, n = Nat.card G * k ∧ ∃ χ : G ≃* Multiplicative (ZMod (Nat.card G)),
      ∀ g, (ψ g).toAdd.val = k * (χ g).toAdd.val := by
  classical
  have he0 : 0 < Nat.card G := Nat.card_pos
  have hdvd : Nat.card G ∣ n := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv,
      Nat.card_eq_fintype_card (α := Multiplicative _), Fintype.card_multiplicative,
      ZMod.card] at h
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (by rw [hk, h, mul_zero]) (NeZero.ne n)
    · exact h
  have hval_dvd : ∀ g, k ∣ (ψ g).toAdd.val := by
    intro g
    have h1 : ψ g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
    have h2 : ((Nat.card G * (ψ g).toAdd.val : ℕ) : ZMod n) = 0 := by
      have h3 := congrArg Multiplicative.toAdd h1
      rw [toAdd_pow, toAdd_one] at h3
      rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id, ← nsmul_eq_mul]
      exact h3
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact Nat.dvd_of_mul_dvd_mul_left he0 ((dvd_of_eq hk.symm).trans h2)
  set t : G → ℕ := fun g => (ψ g).toAdd.val / k with ht_def
  have ht : ∀ g, (ψ g).toAdd.val = k * t g := fun g => (Nat.mul_div_cancel' (hval_dvd g)).symm
  have ht_lt : ∀ g, t g < Nat.card G := by
    intro g
    have h := ZMod.val_lt (ψ g).toAdd
    rw [ht g, hk, mul_comm (Nat.card G) k] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have ht_mul : ∀ g h, t (g * h) = (t g + t h) % Nat.card G := by
    intro g h
    have h1 : (ψ (g * h)).toAdd.val = ((ψ g).toAdd.val + (ψ h).toAdd.val) % n := by
      rw [map_mul, toAdd_mul, ZMod.val_add]
    rw [ht, ht, ht, hk, ← mul_add, mul_comm (Nat.card G) k, Nat.mul_mod_mul_left] at h1
    exact Nat.eq_of_mul_eq_mul_left hk0 h1
  have ht_one : t 1 = 0 := by
    rw [ht_def]
    simp
  let χ₀ : G →* Multiplicative (ZMod (Nat.card G)) :=
    { toFun := fun g => Multiplicative.ofAdd (t g : ZMod (Nat.card G))
      map_one' := by rw [ht_one, Nat.cast_zero, ofAdd_zero]
      map_mul' := fun g h => by
        rw [ht_mul, ← ofAdd_add, ZMod.natCast_mod, Nat.cast_add] }
  have hχ₀ : ∀ g, (χ₀ g).toAdd.val = t g := fun g => by
    change (t g : ZMod (Nat.card G)).val = t g
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ht_lt g)]
  have hinj : Function.Injective χ₀ := by
    intro g h hgh
    apply hψ
    have h1 : t g = t h := by rw [← hχ₀, ← hχ₀, hgh]
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    rw [ht g, ht h, h1]
  have hbij : Function.Bijective χ₀ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_eq_fintype_card (α := Multiplicative _), Fintype.card_multiplicative,
      ZMod.card]
  exact ⟨k, hk, MulEquiv.ofBijective χ₀ hbij, fun g => by
    rw [MulEquiv.ofBijective_apply, hχ₀]
    exact ht g⟩

variable {K : Type v} {L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] {n : ℕ} [NeZero n]

/-- For a cyclic coordinate `χ : Gal(L/K) ≃ ℤ/n`, the carry class of `a` vanishes exactly
when `a` is a norm. -/
theorem cyclicClass_eq_zero_iff (χ : Gal(L/K) ≃* Multiplicative (ZMod n)) (a : Kˣ) :
    cyclicClass K L χ.toMonoidHom a = 0 ↔
      a ∈ Langlands.LocalClassField.normSubgroup K L := by
  have h : ∀ b : Kˣ, cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
      (cyclicCoordinateGenerator_generates χ) (cyclicClass K L χ.toMonoidHom b) =
        Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L b) :=
    cyclicClassNormNormalization.{v, u} K L n χ (cyclicCoordinateGenerator χ)
      (cyclicCoordinateGenerator_generates χ) (χ.apply_symm_apply _)
  rw [← cyclicClass_one χ.toMonoidHom, ← (cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)).injective.eq_iff, h, h, map_one,
    EmbeddingLike.apply_eq_iff_eq]
  exact QuotientGroup.eq_one_iff a

/-- For an injective character `ψ : Gal(L/K) → ℤ/n`, the carry class of `a` vanishes exactly
when `a` is a norm. -/
theorem cyclicClass_eq_zero_iff_of_injective (ψ : Gal(L/K) →* Multiplicative (ZMod n))
    (hψ : Function.Injective ψ) (a : Kˣ) :
    cyclicClass K L ψ a = 0 ↔ a ∈ Langlands.LocalClassField.normSubgroup K L := by
  obtain ⟨k, hn, χ, hval⟩ := exists_mulEquiv_of_injective ψ hψ
  have : NeZero (Nat.card Gal(L/K)) := ⟨Nat.card_pos.ne'⟩
  rw [cyclicClass_eq_of_val_eq hn ψ χ.toMonoidHom hval]
  exact cyclicClass_eq_zero_iff χ a

/-- For a cyclic coordinate, every class of `H²(Gal(L/K), Lˣ)` is a carry class. -/
theorem exists_cyclicClass_eq (χ : Gal(L/K) ≃* Multiplicative (ZMod n))
    (x : relativeCohomology K L 2) : ∃ a : Kˣ, cyclicClass K L χ.toMonoidHom a = x := by
  let e := cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Langlands.LocalClassField.normSubgroup K L)
    (Additive.toMul (e x))
  refine ⟨a, e.injective ?_⟩
  rw [cyclicClassNormNormalization.{v, u} K L n χ (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ) (χ.apply_symm_apply _) a]
  exact congrArg Additive.ofMul ha

end Norm

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] {n : ℕ} [NeZero n]

/-- Inflation of a carry class is the carry class of the inflated character. -/
theorem relativeInflation_cyclicClass [Normal K L] (χ : Gal(L/K) →* Multiplicative (ZMod n))
    (a : Kˣ) :
    relativeInflation K L M 2 (cyclicClass K L χ a) =
      cyclicClass K M (χ.comp (AlgEquiv.restrictNormalHom L)) a :=
  map_cyclicClass _ _ χ a a (UnramifiedInflation.inflationCoefficients_baseUnit K L M a)

/-- Restriction of a carry class is the carry class of the restricted character and the image
of the unit. -/
theorem relativeRestriction_cyclicClass (χ : Gal(M/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    relativeRestriction K L M 2 (cyclicClass K M χ a) =
      cyclicClass L M (χ.comp (AlgEquiv.restrictScalarsHom K))
        (Units.map (algebraMap K L).toMonoidHom a) := by
  refine map_cyclicClass _ _ χ a _ ?_
  apply Units.ext
  exact IsScalarTower.algebraMap_apply K L M (a : K)

end Tower

end CyclicClassAlgebra

end Langlands.ClassFieldTheory.Local
