import Langlands.Global.SiegelFiniteness.Finiteness

/-!
# The entries of a rational matrix relating two points of a Siegel set

If `γ h = h'` for points `h = N diag(ω) A_x κ` and `h' = N' diag(ω') A_{x'} κ'` of a Siegel set
(with the torus coordinates in a common chamber and the key inequality for the compact factors
`A_x⁻¹ h`, `A_{x'}⁻¹ h'`), all entries of `γ` lie in the compact set `entrySet`.
-/

noncomputable section

universe u

open scoped NNReal Matrix
open NumberField

set_option autoImplicit false

namespace Langlands.Global.SiegelFiniteness

open PrimitiveAdelicHeight Automorphic.CuspidalL2

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

theorem realScale_mul_eq_of_fst (s t : ℝ) {z : Adeles F} (hz : z.1 = 0) :
    realScale F s * z = realScale F t * z := by
  apply Prod.ext
  · show PositiveRealIdeles.infiniteRealEmbedding F s * z.1 =
      PositiveRealIdeles.infiniteRealEmbedding F t * z.1
    rw [hz, mul_zero, mul_zero]
  · rfl

theorem fst_mul_mul_eq_zero {p q r : Adeles F} (hq : q.1 = 0) : (p * q * r).1 = 0 := by
  show p.1 * q.1 * r.1 = 0
  rw [hq, mul_zero, zero_mul]

set_option maxHeartbeats 1000000 in
/-- **Entries are bounded.** -/
theorem entries_mem {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)}
    (hΩN : ∀ N ∈ ΩN, IsUnitriangular N) {Q₁ : Set (AdelicGL F n)} {K β : ℝ} (hK : 0 ≤ K)
    (hβ : 0 ≤ β)
    (hkey : ∀ (x x' : Fin n → ℝ) (q q' : AdelicGL F n), q ∈ Q₁ → q' ∈ Q₁ →
      ∀ γ : RationalGL F n,
        AdelicGL.rational F n γ * (AdelicGL.ofInfinite F n (torInf F n x) * q) =
          AdelicGL.ofInfinite F n (torInf F n x') * q' →
        ∀ t j : Fin n, (γ⁻¹ : RationalGL F n).val t j ≠ 0 → x' j ≤ x t + β)
    (γ : RationalGL F n) {Ngl Ngl' : AdelicGL F n} {ω ω' : Fin n → Ideles F}
    {x x' : Fin n → ℝ} {κ κ' : AdelicGL F n}
    (hN : (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) ∈ ΩN)
    (hN' : (Ngl' : Matrix (Fin n) (Fin n) (Adeles F)) ∈ ΩN)
    (hω : ∀ i, ω i ∈ C) (hω' : ∀ i, ω' i ∈ C)
    (hκ : κ ∈ standardCompact F n) (hκ' : κ' ∈ standardCompact F n)
    (hx : Chamber K x) (hx' : Chamber K x')
    (hq : (AdelicGL.ofInfinite F n (torInf F n x))⁻¹ *
      (Ngl * diagonalGL ω * AdelicGL.ofInfinite F n (torInf F n x) * κ) ∈ Q₁)
    (hq' : (AdelicGL.ofInfinite F n (torInf F n x'))⁻¹ *
      (Ngl' * diagonalGL ω' * AdelicGL.ofInfinite F n (torInf F n x') * κ') ∈ Q₁)
    (hγ : AdelicGL.rational F n γ *
        (Ngl * diagonalGL ω * AdelicGL.ofInfinite F n (torInf F n x) * κ) =
      Ngl' * diagonalGL ω' * AdelicGL.ofInfinite F n (torInf F n x') * κ') (i j : Fin n) :
    ((AdelicGL.rational F n γ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j ∈
      entrySet F n ΩN C ((β + 2 * n * K) + n * K + n * ((β + 2 * n * K) + β + 2 * n * K)) := by
  set A := AdelicGL.ofInfinite F n (torInf F n x) with hAdef
  set A' := AdelicGL.ofInfinite F n (torInf F n x') with hA'def
  set h := Ngl * diagonalGL ω * A * κ with hhdef
  set h' := Ngl' * diagonalGL ω' * A' * κ' with hh'def
  -- the key inequality in both directions
  have k1 : ∀ t j, (γ⁻¹ : RationalGL F n).val t j ≠ 0 → x' j ≤ x t + β :=
    hkey x x' _ _ hq hq' γ (by rw [mul_inv_cancel_left, mul_inv_cancel_left]; exact hγ)
  have k2 : ∀ t j, γ.val t j ≠ 0 → x j ≤ x' t + β := by
    intro t j htj
    refine hkey x' x _ _ hq' hq γ⁻¹ ?_ t j (by rwa [inv_inv])
    rw [mul_inv_cancel_left, mul_inv_cancel_left, ← hγ, map_inv, inv_mul_cancel_left]
  -- comparability
  have c1 : ∀ i, x' i ≤ x i + (β + 2 * n * K) :=
    le_add_of_key hK hx hx' k1 fun i => exists_lowerLeft_ne_zero γ⁻¹ i
  -- a large drop makes `γ`, hence the compact part, block upper triangular
  have hblock : ∀ p q : Fin n, p.val + 1 = q.val →
      (β + 2 * n * K) + β + 2 * n * K < x p - x q →
      IsBlockUpper q.val ((κ' * κ⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) := by
    intro p q hpq hdrop
    refine isBlockUpper_compactPart (hΩN _ hN).1 (hΩN _ hN').1 hγ ?_
    intro t j ht hj
    have := not_of_drop hK hx c1 k2 p q hpq hdrop t j ht hj
    push Not at this
    change algebraMap F (Adeles F) (γ.val t j) = 0
    rw [this, map_zero]
  have hm : κ' * κ⁻¹ ∈ standardCompact F n :=
    mul_mem hκ' (inv_mem hκ)
  -- the middle factor
  set M := diagonalGL ω' * A' * (κ' * κ⁻¹) * A⁻¹ * (diagonalGL ω)⁻¹ with hMdef
  have hMmem : ∀ a b, (M : Matrix (Fin n) (Fin n) (Adeles F)) a b ∈
      middleSet F n C ((β + 2 * n * K) + n * K + n * ((β + 2 * n * K) + β + 2 * n * K)) := by
    intro a b
    rw [hMdef, hAdef, hA'def, middle_apply]
    have hZ : (ω' a).val * ((κ' * κ⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) a b *
        ((ω b)⁻¹ : Ideles F).val ∈ ⋃ a : Fin n, ⋃ b : Fin n,
          (fun p : Ideles F × AdelicGL F n × Ideles F =>
            p.1.val * (p.2.1 : Matrix (Fin n) (Fin n) (Adeles F)) a b *
              (p.2.2⁻¹ : Ideles F).val) ''
            (C ×ˢ (standardCompact F n : Set (AdelicGL F n)) ×ˢ C) :=
      Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ⟨(ω' a, κ' * κ⁻¹, ω b),
        ⟨hω' a, hm, hω b⟩, rfl⟩⟩⟩
    have hG : 0 ≤ (β + 2 * n * K) + β + 2 * n * K := by positivity
    rcases le_or_exists_drop hK hx' hG c1 a b with hle | ⟨p, q, hpq, haq, hqb, hdrop⟩
    · exact ⟨(Real.exp (x' a - x b), _), ⟨⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr hle⟩, hZ⟩,
        rfl⟩
    · have hzero := infinite_entry_eq_zero hm (hblock p q hpq hdrop) a b haq hqb
      refine ⟨(0, _), ⟨⟨le_rfl, (Real.exp_pos _).le⟩, hZ⟩, ?_⟩
      exact realScale_mul_eq_of_fst _ _ (fst_mul_mul_eq_zero hzero)
  -- the factorization of `γ`
  have hγeq : AdelicGL.rational F n γ = Ngl' * M * Ngl⁻¹ := by
    rw [eq_mul_inv_of_mul_eq hγ, hMdef, hh'def, hhdef]
    group
  rw [hγeq, Units.val_mul, Units.val_mul, inv_val_eq_adjugate (hΩN _ hN)]
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, ⟨((Ngl' : Matrix (Fin n) (Fin n) (Adeles F)),
    (M : Matrix (Fin n) (Fin n) (Adeles F)), (Ngl : Matrix (Fin n) (Fin n) (Adeles F))),
    ⟨hN', fun a _ b _ => hMmem a b, hN⟩, rfl⟩⟩⟩

end Langlands.Global.SiegelFiniteness
