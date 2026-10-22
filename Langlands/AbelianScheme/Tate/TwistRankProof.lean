import Langlands.AbelianScheme.Tate.TwistRankStatement
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.Padics.RingHoms

namespace Langlands.TateTwist

universe u

namespace RankOne

variable {Ω : Type u} [Field Ω] {p : ℕ}

/-- Successive `p`-th roots in a separably closed field, starting from `ζ`. -/
noncomputable def tower [IsSepClosed Ω] [NeZero (p : Ω)] (ζ : Ω) : ℕ → Ω
  | 0 => ζ
  | n + 1 => Classical.choose (IsSepClosed.exists_pow_nat_eq (tower ζ n) p)

variable [IsSepClosed Ω] [NeZero (p : Ω)]

lemma tower_succ_pow (ζ : Ω) (n : ℕ) : tower (p := p) ζ (n + 1) ^ p = tower (p := p) ζ n :=
  Classical.choose_spec (IsSepClosed.exists_pow_nat_eq (tower (p := p) ζ n) p)

/-- The `p ^ n`-th member of the compatible system of roots. -/
noncomputable def root (ζ : Ω) (n : ℕ) : Ω := tower (p := p) ζ n ^ p

lemma root_succ_pow (ζ : Ω) (n : ℕ) : root (p := p) ζ (n + 1) ^ p = root (p := p) ζ n := by
  rw [root, root, tower_succ_pow]

variable [Fact p.Prime]

lemma tower_isPrimitiveRoot {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    IsPrimitiveRoot (tower (p := p) ζ n) (p ^ (n + 1)) := by
  induction n with
  | zero => simpa [tower] using hζ
  | succ n ih =>
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [pow_succ' p n, pow_mul, tower_succ_pow]
      exact ih.pow_ne_one_of_pos_of_lt (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
        (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self n))
    · rw [pow_succ' p (n + 1), pow_mul, tower_succ_pow]
      exact ih.pow_eq_one

lemma root_isPrimitiveRoot {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    IsPrimitiveRoot (root (p := p) ζ n) (p ^ n) :=
  (tower_isPrimitiveRoot hζ n).pow (pow_pos (Fact.out : p.Prime).pos _) (pow_succ' p n)

/-- The chosen generator of the actual level `p ^ n`. -/
noncomputable def generator {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) : Level Ω (p ^ n) :=
  Additive.ofMul (root_isPrimitiveRoot hζ n).toRootsOfUnity

lemma generator_val {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    (((Additive.toMul (generator hζ n) : rootsOfUnity (p ^ n) Ω) : Ωˣ) : Ω) =
      root (p := p) ζ n := rfl

lemma zmod_smul_generator_val {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) (k : ZMod (p ^ n)) :
    (((Additive.toMul (k • generator hζ n) : rootsOfUnity (p ^ n) Ω) : Ωˣ) : Ω) =
      root (p := p) ζ n ^ k.val := by
  have h := congrArg (fun y : Additive Ωˣ => ((Additive.toMul y : Ωˣ) : Ω))
    (toUnit_zmod_smul Ω (p ^ n) k (generator hζ n))
  simpa [toUnit, generator_val] using h

lemma transition_generator {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    transition Ω (pow_dvd_pow p (Nat.le_succ n)) (generator hζ (n + 1)) = generator hζ n := by
  apply toUnit_injective Ω (p ^ n)
  rw [toUnit_transition_succ]
  apply Additive.toMul.injective
  apply Units.ext
  change ((((Additive.toMul (generator hζ (n + 1)) : rootsOfUnity _ Ω) : Ωˣ) ^ p : Ωˣ) : Ω) =
    (((Additive.toMul (generator hζ n) : rootsOfUnity _ Ω) : Ωˣ) : Ω)
  rw [Units.val_pow_eq_pow_val, generator_val, generator_val, root_succ_pow]

lemma eq_zero_of_zmod_smul_generator {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    {k : ZMod (p ^ n)} (h : k • generator hζ n = 0) : k = 0 := by
  have hv := zmod_smul_generator_val hζ n k
  rw [h] at hv
  have h1 : root (p := p) ζ n ^ k.val = 1 := by rw [← hv]; rfl
  rw [← ZMod.natCast_zmod_val k, ZMod.natCast_eq_zero_iff]
  exact (root_isPrimitiveRoot hζ n).dvd_of_pow_eq_one _ h1

lemma exists_zmod_smul_generator {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ)
    (x : Level Ω (p ^ n)) : ∃ k : ZMod (p ^ n), k • generator hζ n = x := by
  obtain ⟨i, hi, hix⟩ := (root_isPrimitiveRoot hζ n).eq_pow_of_pow_eq_one
    (ξ := (((Additive.toMul x : rootsOfUnity (p ^ n) Ω) : Ωˣ) : Ω))
    (by rw [← Units.val_pow_eq_pow_val, (Additive.toMul x).property, Units.val_one])
  refine ⟨(i : ZMod (p ^ n)), ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [zmod_smul_generator_val, ZMod.val_cast_of_lt hi, hix]

/-- The linear map sending `a` to the compatible family `a • generator n`. -/
noncomputable def toIntegral {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) : ℤ_[p] →ₗ[ℤ_[p]] Integral Ω p :=
  lift Ω p (fun n => LinearMap.toSpanSingleton ℤ_[p] _ (generator hζ n)) (by
    intro n a
    simp only [LinearMap.toSpanSingleton_apply]
    rw [transition_smul Ω p (Nat.le_succ n), transition_generator])

lemma evaluation_toIntegral {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) (a : ℤ_[p]) :
    evaluation Ω p n (toIntegral hζ a) = PadicInt.toZModPow n a • generator hζ n := rfl

lemma toIntegral_injective {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (toIntegral hζ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_zero]
  apply eq_zero_of_zmod_smul_generator hζ
  rw [← evaluation_toIntegral, ha, map_zero]

lemma toIntegral_surjective {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    Function.Surjective (toIntegral hζ) := by
  intro x
  choose k hk using fun n => exists_zmod_smul_generator hζ n (evaluation Ω p n x)
  have hcompat : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (k (n + 1)) =
      k n := by
    intro n
    rw [← sub_eq_zero]
    apply eq_zero_of_zmod_smul_generator hζ
    rw [sub_smul, sub_eq_zero, hk n, ← evaluation_transition Ω p n x, ← hk (n + 1),
      transition_zmod_smul, transition_generator]
  have hi : ∀ i, (p : ℤ) ^ i ∣ ((k (i + 1)).val : ℤ) - ((k i).val : ℤ) := by
    intro i
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub ((k i).val : ℤ) ((k (i + 1)).val : ℤ)
      (p ^ i)).mp (by
        rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_val,
          ← ZMod.castHom_apply (h := pow_dvd_pow p (Nat.le_succ i)), hcompat])
    exact_mod_cast h
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun i => ((k i).val : ℤ)) p hi), ?_⟩
  apply Subtype.ext
  funext n
  change evaluation Ω p n (toIntegral hζ _) = evaluation Ω p n x
  rw [evaluation_toIntegral, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p hi]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  exact hk n

end RankOne

/-- Proof of `Langlands.TateTwist.IntegralRankOne`. -/
theorem integralRankOne (Ω : Type u) [Field Ω] (p : ℕ) [Fact p.Prime] :
    IntegralRankOne Ω p := by
  intro hsep hp
  have : NeZero (p : Ω) := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  exact ⟨LinearEquiv.ofBijective (RankOne.toIntegral hζ)
    ⟨RankOne.toIntegral_injective hζ, RankOne.toIntegral_surjective hζ⟩⟩

end Langlands.TateTwist
