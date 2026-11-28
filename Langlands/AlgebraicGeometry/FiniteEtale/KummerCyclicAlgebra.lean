import Langlands.AlgebraicGeometry.FiniteEtale.KummerCovers

/-! # Kummer algebras from unit eigenvectors

Let `A` be an algebra over a ring `R`, let `B` be an `A`-algebra with an `A`-algebra
endomorphism `σ`, and let `ζ` be an `m`-th root of unity of `R`. An `m`-th root `v ∈ B` of an
element `a ∈ A` gives an `A`-algebra map `A[X]/(X^m - a) → B`, `X ↦ v`; when `σ v = ζ v`, this
map intertwines `X ↦ ζ X` with `σ`.

Over `A = R[1/t]`, for a strictly Henselian local domain `R`, a prime element `t` and a prime
`ℓ` invertible in `R`, let `v` be a unit eigenvector of `σ` with eigenvalue a nontrivial `ℓ`-th
root of unity in `R`. If `v^ℓ` is the image of a unit of `A`, multiplying `v` by units from `A`
and taking a power prime to `ℓ` makes its `ℓ`-th power `1` or `t`. This gives an equivariant
map from `A[X]/(X^ℓ - 1)` or from `A[X]/(X^ℓ - t)` to `B` for a nontrivial `ℓ`-th root of unity.
-/

noncomputable section

universe u

open Polynomial IsLocalRing

namespace Langlands.AlgebraicGeometry.FiniteEtale

section Lift

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The `A`-algebra map `A[X]/(X^m - a) → B` sending `X` to an `m`-th root `v` of `a`. -/
def kummerLift (a : A) (m : ℕ) (v : B) (hv : v ^ m = algebraMap A B a) :
    KummerRootAlgebra a m →ₐ[A] B :=
  AdjoinRoot.liftAlgHom (X ^ m - C a) (Algebra.ofId A B) v (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hv]
    simp)

@[simp]
theorem kummerLift_root (a : A) (m : ℕ) (v : B) (hv : v ^ m = algebraMap A B a) :
    kummerLift a m v hv (AdjoinRoot.root _) = v :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- If `σ v = ζ v`, the map `X ↦ v` intertwines `X ↦ ζ X` with `σ`. -/
theorem comp_kummerLift (R : Type*) [CommRing R] [Algebra R A] (σ : B →ₐ[A] B) (a : A)
    (m : ℕ) (v : B) (hv : v ^ m = algebraMap A B a) (ζ : rootsOfUnity m R)
    (hσ : σ v = algebraMap A B (algebraMap R A ((ζ : Rˣ) : R)) * v) :
    σ.comp (kummerLift a m v hv) = (kummerLift a m v hv).comp (kummerScale R a m ζ) := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, kummerLift_root, kummerScale_root, map_mul, AlgHom.commutes, hσ]

end Lift

section Normalize

variable {R : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] {t : R} {B : Type u} [CommRing B]
  [Algebra (Localization.Away t) B]

/-- **Kummer normalization of a unit eigenvector.** Let `R` be a strictly Henselian local
domain, `t` a prime element, `ℓ` a prime invertible in `R`, and `σ` an endomorphism of an
`R[1/t]`-algebra `B`. If a unit `v` of `B` satisfies `σ v = ζ v` for an `ℓ`-th root of unity
`ζ ≠ 1` and `v^ℓ` is the image of a unit of `R[1/t]`, then for `a = 1` or `a = t` there is an
`ℓ`-th root of unity `η ≠ 1` and an `R[1/t]`-algebra map `ψ : R[1/t][X]/(X^ℓ - a) → B` with
`σ ∘ ψ = ψ ∘ (X ↦ η X)`. -/
theorem exists_kummerLift_of_unit_eigenvector (ht : Prime t) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓR : IsUnit (ℓ : R)) (σ : B →ₐ[Localization.Away t] B) (ζ : rootsOfUnity ℓ R)
    (hζ : ζ ≠ 1) (v : Bˣ)
    (hv : σ v = algebraMap (Localization.Away t) B
      (algebraMap R (Localization.Away t) ((ζ : Rˣ) : R)) * v)
    (w : (Localization.Away t)ˣ) (hw : (v : B) ^ ℓ = algebraMap (Localization.Away t) B w) :
    ∃ a : Localization.Away t, (a = 1 ∨ a = algebraMap R (Localization.Away t) t) ∧
      ∃ (η : rootsOfUnity ℓ R) (ψ : KummerRootAlgebra a ℓ →ₐ[Localization.Away t] B),
        η ≠ 1 ∧ σ.comp ψ = ψ.comp (kummerScale R a ℓ η) := by
  set A := Localization.Away t
  set f : Aˣ →* Bˣ := Units.map (algebraMap A B).toMonoidHom with hf
  set T : Aˣ := (IsLocalization.Away.algebraMap_isUnit (S := A) t).unit with hT
  have hTval : ((T : Aˣ) : A) = algebraMap R A t := IsUnit.unit_spec _
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hζℓ : ((ζ : Rˣ) : R) ^ ℓ = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ (ζ : Rˣ)).mp ζ.2, Units.val_one]
  -- the image of `ζ` in `B`
  set c : B := algebraMap A B (algebraMap R A ((ζ : Rˣ) : R)) with hc
  -- `σ` on images of units of `A`
  have hσf : ∀ y : Aˣ, σ ((f y : Bˣ) : B) = (f y : B) := fun y => σ.commutes (y : A)
  -- decompose `w = u T^k`
  obtain ⟨u, k, hwu⟩ :=
    Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits.exists_eq_unit_mul_zpow ht w
  obtain ⟨u₀, hu₀⟩ := Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits.exists_pow_eq_of_isUnit
    hℓR hℓ0 u.isUnit
  have hu₀unit : IsUnit u₀ := by
    rw [← isUnit_pow_iff hℓ0, hu₀]
    exact u.isUnit
  set U₀ : Rˣ := hu₀unit.unit with hU₀
  have hU₀pow : U₀ ^ ℓ = u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hU₀, IsUnit.unit_spec, hu₀]
  set gR : Rˣ →* Aˣ := Units.map (algebraMap R A).toMonoidHom with hgR
  set q : ℤ := k / ℓ
  set k₀ : ℤ := k % ℓ
  have hk : k = ℓ * q + k₀ := (Int.mul_ediv_add_emod k ℓ).symm
  have hk₀nn : 0 ≤ k₀ := Int.emod_nonneg k (by exact_mod_cast hℓ0)
  have hk₀lt : k₀ < ℓ := Int.emod_lt_of_pos k (by exact_mod_cast hℓ.pos)
  -- the first normalization `v₁ = v / (u₀ T^q)`
  set V : Aˣ := gR U₀ * T ^ q
  set v₁ : Bˣ := v * f V⁻¹ with hv₁
  have hv₁pow : v₁ ^ ℓ = f (T ^ k₀) := by
    have hw' : v ^ ℓ = f w := Units.ext (by rw [Units.val_pow_eq_pow_val, hw]; rfl)
    have hV : V ^ ℓ * T ^ k₀ = w := by
      rw [hwu, mul_pow, ← map_pow, hU₀pow, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add,
        mul_comm (q : ℤ) _, ← hk]
    rw [hv₁, mul_pow, hw', ← map_pow, ← hV, inv_pow, ← map_mul, mul_comm (V ^ ℓ), mul_assoc,
      mul_inv_cancel, mul_one]
  have hσv₁ : σ (v₁ : B) = c * v₁ := by
    rw [hv₁, Units.val_mul, map_mul, hv, hσf, mul_assoc]
  -- case distinction on `k₀`
  by_cases hk₀ : k₀ = 0
  · refine ⟨1, Or.inl rfl, ζ, kummerLift 1 ℓ (v₁ : B) ?_, hζ, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, hv₁pow, hk₀, zpow_zero, map_one, Units.val_one, map_one]
    · exact comp_kummerLift R σ 1 ℓ _ _ ζ hσv₁
  · -- `k₀` is invertible modulo `ℓ`
    have hk₀pos : 0 < k₀ := lt_of_le_of_ne hk₀nn (Ne.symm hk₀)
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, k₀ = n₀ := ⟨k₀.toNat, (Int.toNat_of_nonneg hk₀nn).symm⟩
    have hn₀pos : 0 < n₀ := by exact_mod_cast hn₀ ▸ hk₀pos
    have hn₀lt : n₀ < ℓ := by exact_mod_cast hn₀ ▸ hk₀lt
    have hcop : Nat.Coprime n₀ ℓ :=
      Nat.Coprime.symm ((hℓ.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hn₀pos hn₀lt))
    obtain ⟨k₁, -, hk₁⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
    set s : ℕ := n₀ * k₁ / ℓ
    have hs : n₀ * k₁ = ℓ * s + 1 := by
      have := Nat.div_add_mod (n₀ * k₁) ℓ
      rw [hk₁] at this
      exact this.symm
    -- the second normalization `v₂ = v₁^{k₁} / T^s`
    set v₂ : Bˣ := v₁ ^ k₁ * f (T ^ s)⁻¹ with hv₂
    have hA : (T ^ k₀) ^ k₁ * ((T ^ s)⁻¹) ^ ℓ = T := by
      rw [hn₀, zpow_natCast, ← pow_mul, hs, pow_add, pow_one, mul_comm ℓ s, pow_mul, inv_pow,
        mul_comm ((T ^ s) ^ ℓ) T, mul_assoc, mul_inv_cancel, mul_one]
    have hv₂pow : v₂ ^ ℓ = f T := by
      rw [hv₂, mul_pow, ← pow_mul, mul_comm k₁ ℓ, pow_mul, hv₁pow, ← map_pow, ← map_pow,
        ← map_mul, hA]
    set η : rootsOfUnity ℓ R := ζ ^ k₁
    have hη : η ≠ 1 := by
      intro h
      have := Fact.mk hℓ
      have hord : orderOf ζ = ℓ := orderOf_eq_prime (by
        apply Subtype.ext
        simpa using (mem_rootsOfUnity ℓ (ζ : Rˣ)).mp ζ.2) hζ
      have hdvd : ℓ ∣ k₁ := hord ▸ orderOf_dvd_of_pow_eq_one h
      have : ℓ ∣ n₀ * k₁ := dvd_mul_of_dvd_right hdvd n₀
      rw [hs] at this
      have h1 : ℓ ∣ 1 := (Nat.dvd_add_right (dvd_mul_right ℓ s)).mp this
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
    have hσv₂ : σ (v₂ : B) = algebraMap A B (algebraMap R A ((η : Rˣ) : R)) * v₂ := by
      rw [hv₂, Units.val_mul, map_mul, hσf, Units.val_pow_eq_pow_val, map_pow, hσv₁, mul_pow]
      simp only [η, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, map_pow, hc, mul_assoc]
    refine ⟨algebraMap R A t, Or.inr rfl, η, kummerLift _ ℓ (v₂ : B) ?_, hη, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, hv₂pow, ← hTval]
      rfl
    · exact comp_kummerLift R σ _ ℓ _ _ η hσv₂

end Normalize

end Langlands.AlgebraicGeometry.FiniteEtale
