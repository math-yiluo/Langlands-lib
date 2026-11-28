import Langlands.BushnellKutzko.ShiftedSimpleHGroup
import Langlands.BushnellKutzko.HeisenbergCharacterLocalData

/-! # Simple characters on the unipotent parts of `H^m` (BK93 (8.2.5)(iii))

For complementary idempotents `e₁, e₂` of `𝔅`, a simple character is trivial on the elements
`1 + x` of `H^m` with `x = e₁ x e₂`: conjugation by `ϖ_F^k e₁ + e₂ ∈ B^×` replaces `x` by
`ϖ_F^k x`, and simple characters are trivial on deep unit groups. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The unit `a e₁ + e₂` for complementary idempotents and `a ≠ 0`. -/
def blockScalar {e₁ e₂ : A} (hadd : e₁ + e₂ = 1) (hmul : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    {a : F} (ha : a ≠ 0) : G where
  val := a • e₁ + e₂
  inv := a⁻¹ • e₁ + e₂
  val_inv := by
    have he₁ : e₁ * e₁ = e₁ := by
      calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, hmul, add_zero]
        _ = e₁ := by rw [hadd, mul_one]
    have he₂ : e₂ * e₂ = e₂ := by
      calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, hmul, zero_add]
        _ = e₂ := by rw [hadd, one_mul]
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, he₁, mul_inv_cancel₀ ha, one_smul,
      smul_mul_assoc, hmul, smul_zero, add_zero, mul_smul_comm, h₂₁, smul_zero, zero_add, he₂,
      hadd]
  inv_val := by
    have he₁ : e₁ * e₁ = e₁ := by
      calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, hmul, add_zero]
        _ = e₁ := by rw [hadd, mul_one]
    have he₂ : e₂ * e₂ = e₂ := by
      calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, hmul, zero_add]
        _ = e₂ := by rw [hadd, one_mul]
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, he₁, inv_mul_cancel₀ ha, one_smul,
      smul_mul_assoc, hmul, smul_zero, add_zero, mul_smul_comm, h₂₁, smul_zero, zero_add, he₂,
      hadd]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockScalar_val {e₁ e₂ : A} (hadd : e₁ + e₂ = 1) (hmul : e₁ * e₂ = 0)
    (h₂₁ : e₂ * e₁ = 0) {a : F} (ha : a ≠ 0) :
    ((blockScalar hadd hmul h₂₁ ha : G) : A) = a • e₁ + e₂ := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation by `a e₁ + e₂` multiplies the block `e₁ A e₂` by `a`. -/
theorem blockScalar_conj_sub_one {e₁ e₂ : A} (hadd : e₁ + e₂ = 1) (hmul : e₁ * e₂ = 0)
    (h₂₁ : e₂ * e₁ = 0) {a : F} (ha : a ≠ 0) (g : G)
    (hg : e₁ * ((g : A) - 1) * e₂ = (g : A) - 1) :
    ((blockScalar hadd hmul h₂₁ ha * g * (blockScalar hadd hmul h₂₁ ha)⁻¹ : G) : A) - 1 =
      a • ((g : A) - 1) := by
  set x := (g : A) - 1 with hx
  have he₁ : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, hmul, add_zero]
      _ = e₁ := by rw [hadd, mul_one]
  have he₂ : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, hmul, zero_add]
      _ = e₂ := by rw [hadd, one_mul]
  have h1x : e₁ * x = x := by rw [← hg, ← mul_assoc, ← mul_assoc, he₁]
  have h2x : e₂ * x = 0 := by rw [← hg, ← mul_assoc, ← mul_assoc, h₂₁, zero_mul, zero_mul]
  have hx1 : x * e₁ = 0 := by rw [← hg, mul_assoc, h₂₁, mul_zero]
  have hx2 : x * e₂ = x := by rw [← hg, mul_assoc, he₂]
  have hgx : (g : A) = 1 + x := by rw [hx]; abel
  have hinv : (((blockScalar hadd hmul h₂₁ ha)⁻¹ : G) : A) = a⁻¹ • e₁ + e₂ := rfl
  have hTT : (a • e₁ + e₂) * (a⁻¹ • e₁ + e₂) = 1 := by
    rw [← blockScalar_val hadd hmul h₂₁ ha, ← hinv, Units.mul_inv]
  have hTx : (a • e₁ + e₂) * x = a • x := by rw [add_mul, smul_mul_assoc, h1x, h2x, add_zero]
  have hxT' : x * (a⁻¹ • e₁ + e₂) = x := by
    rw [mul_add, mul_smul_comm, hx1, smul_zero, zero_add, hx2]
  calc ((blockScalar hadd hmul h₂₁ ha * g * (blockScalar hadd hmul h₂₁ ha)⁻¹ : G) : A) - 1 =
      (a • e₁ + e₂) * (1 + x) * (a⁻¹ • e₁ + e₂) - 1 := by
        rw [Units.val_mul, Units.val_mul, blockScalar_val, hinv, hgx]
    _ = (a • e₁ + e₂) * (a⁻¹ • e₁ + e₂) + ((a • e₁ + e₂) * x) * (a⁻¹ • e₁ + e₂) - 1 := by
        rw [mul_add (a • e₁ + e₂) 1 x, mul_one, add_mul]
    _ = a • x := by rw [hTT, hTx, smul_mul_assoc, hxT']; abel

/-- **BK93 (8.2.5)(iii) for simple characters.** Let `[𝔄, n, 0, β]` be simple,
`θ ∈ C(𝔄, m−1, β)` on `H^m`, and `e₁, e₂` complementary idempotents of `𝔅`. Then `θ` is
trivial on the elements `h = 1 + x` of `H^m` with `x = e₁ x e₂`. -/
theorem simpleCharacter_eq_one_of_block (S : Stratum 𝒪[F] F V) (h0 : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    {e₁ e₂ : A} (hadd : e₁ + e₂ = 1) (hmul : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    (he₁b : e₁ * S.b = S.b * e₁) (he₂b : e₂ * S.b = S.b * e₂)
    (h : simpleHGroup S.chain S.n S.b q.tail (i + 1))
    (hh : e₁ * (((h : G) : A) - 1) * e₂ = ((h : G) : A) - 1) : θ h = 1 := by
  have := S.chain.finiteDimensional
  obtain ⟨N, hN1, hN⟩ := simpleCharacter_trivial_on_deep_units S.chain S.n hψ S.b q.tail i hθ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h0'
    exact hϖ.ne_zero (Subtype.ext h0')
  set a : F := (ϖ : F) ^ N with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ hϖ0
  set t := blockScalar hadd hmul h₂₁ ha0 with ht
  have htb : (t : A) * S.b = S.b * (t : A) := by
    rw [ht, blockScalar_val, add_mul, mul_add, smul_mul_assoc, he₁b, mul_smul_comm, he₂b]
  have hx1 : ((h : G) : A) - 1 ∈ S.chain.endFiltration 1 :=
    S.chain.endFiltration_antitone (by push_cast; omega)
      (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (i + 1) h.2).2.2
  have hconj := blockScalar_conj_sub_one hadd hmul h₂₁ ha0 (h : G) hh
  have hdeep : a • (((h : G) : A) - 1) ∈ S.chain.endFiltration N := by
    have h1 := (S.chain.uniformizer_pow_end_mem_iff hϖ N 1 _).mpr hx1
    exact S.chain.endFiltration_antitone (by
      have := S.chain.period_pos
      nlinarith) h1
  have hU : t * (h : G) * t⁻¹ ∈ S.chain.unitFiltration N :=
    mem_unitFiltration_of_sub_one_mem S.chain hN1 (by rw [hconj]; exact hdeep)
  obtain ⟨hmem, hθ1⟩ := hN _ hU
  rw [← simpleCharacter_conj_of_commute S h0 hs q i hin hcrit hψ hθ htb h hmem]
  exact hθ1

end Langlands.BushnellKutzko.SplitBlocks
