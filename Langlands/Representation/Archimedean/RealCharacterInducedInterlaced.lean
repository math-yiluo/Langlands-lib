import Langlands.Representation.Archimedean.RealCharacterInducedSwap
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror
import Langlands.Representation.Archimedean.RealOrthogonalUncertainty
import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-!
# Bijective character-induced swaps at interlaced integral parameters

Extracts the actual bijective intertwiners constructed by the two tail cases in
`RealCharacterInducedSwap`. Landing and uncertainty are discharged by their proofs.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealCharacterInducedInterlaced

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap
open RealCharacterInducedPushforward
open Langlands.LocalFactor.Archimedean

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- Tail-first bijection, from the induction-first space to the character-first space. -/
theorem exists_bijective_tail_first {m : ℕ} (hm0 : 0 < m)
    (hml : m < d.weight.natAbs) (hw : (chB d).exponent - c.exponent = -(m : ℂ))
    (hpar : (m + c.parity.val) % 2 = 1) :
    ∃ T : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lCD c d),
      Function.Bijective T ∧ IsRealIntertwinerModulo 3 (lDC c d) (lCD c d) ⊥ T := by
  have hLI := RealSwapLandingIntegral.inducedFirst
  have hU := RealOrthogonalUncertainty.realOrthogonalBlockUncertainty
  have hw' : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(m : ℂ) := hw
  have hε := parity_cases c
  have hparT : Even ((m : ℤ) - 1 - (c.parity.val : ℤ)) := by
    rw [Int.even_iff]
    omega
  have hσ : ((-1 : ℂ) ^ c.parity.val) ^ 2 = 1 := neg_one_pow_sq_fin c.parity
  -- the tail map `A₁` along `r₁`
  have hs₁ := isSymmetric_tailMultiplier hm0 hε hparT hσ
  have hA1 := dataA1 c d rfl hs₁
  have hrec₁ : IsRecurrent (1 - (m : ℂ)) (c.parity.val : ℤ)
      (tailMultiplier m (c.parity.val : ℤ) ((-1) ^ c.parity.val)) :=
    isRecurrent_tailMultiplier hm0 hε hparT hσ
  have hA1m : IsRealIntertwinerModulo 3 (lDC c d) (lM c d) ⊥ (blockFrobMap hA1) := by
    refine isRealIntertwinerModulo_blockFrobMap hA1 ?_ ⊥
    rw [posExp_lDC_1, posExp_lDC_2,
      show d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent + 1 = 1 - (m : ℂ) by
        linear_combination hw']
    exact hrec₁
  -- the generic swap `A₀` along `r₀`, with `ν₀ = a - s = ℓ - m₀`
  have hν₀ : (chA d).exponent - c.exponent = ((d.weight.natAbs - m : ℕ) : ℂ) := by
    rw [Nat.cast_sub hml.le, chA_exponent]
    linear_combination hw'
  have hν₀re : 0 < (((d.weight.natAbs - m : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast Nat.sub_pos_of_lt hml
  have hε₀ := pairParity_eq c (chA d)
  have hs₀ := isSymmetric_genericMultiplier ((d.weight.natAbs - m : ℕ) : ℂ) hε₀
  have hA0 := dataA0 c d hs₀
  have hrec₀ : IsRecurrent (((d.weight.natAbs - m : ℕ) : ℂ) + 1) (pairParity c (chA d))
      (genericMultiplier ((d.weight.natAbs - m : ℕ) : ℂ) (pairParity c (chA d))) :=
    isRecurrent_genericMultiplier hν₀re hε₀
  have hA0m : IsRealIntertwinerModulo 3 (lM c d) (lP c d) ⊥ (blockFrobMap hA0) := by
    refine isRealIntertwinerModulo_blockFrobMap hA0 ?_ ⊥
    rw [posExp_lM_0, posExp_lM_1, hν₀]
    exact hrec₀
  have hA0i : Function.Injective (blockFrobMap hA0) :=
    frob_injective_of_ne_zero hA0 fun k _ => genericMultiplier_ne_zero hν₀re hε₀ (fun i h => by
      have e : ((d.weight.natAbs - m : ℕ) : ℤ) = pairParity c (chA d) + 2 * i + 1 := by
        exact_mod_cast h
      rw [pairParity_c_chA] at e
      omega) k
  -- the composite lands in the standard module of `[c, d]`
  have hrec₀' : IsRecurrent (1 - (m : ℂ) + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      (genericMultiplier ((d.weight.natAbs - m : ℕ) : ℂ) (pairParity c (chA d))) := by
    rw [show 1 - (m : ℂ) + (d.weight.natAbs : ℂ) = ((d.weight.natAbs - m : ℕ) : ℂ) + 1 by
      rw [Nat.cast_sub hml.le]
      ring]
    exact isRecurrent_of_even hrec₀ (even_class_c_chA c d)
  have hland : ∀ f : KF 3 (lDC c d), ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 1 k
        ((blockFrobMap hA0 (blockFrobMap hA1 f) : KF 3 (lP c d)) :
          Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := fun f =>
    hLI c d (1 - (m : ℂ)) _ _ (f : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hA1 f : KF 3 (lM c d)) : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hA0 (blockFrobMap hA1 f) : KF 3 (lP c d)) :
        Langlands.GeneralLinear 3 ℝ → ℂ)
      hrec₁ hs₁ hrec₀' (isSymmetric_of_even hs₀ (even_class_c_chA c d) (sign_class_c_chA c d))
      f.2 (continuous_coe _) (continuous_coe _)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hA1 f hg k)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hA0 _ hg k)
  let T1 : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lP c d) := blockFrobMap hA0 ∘ₗ blockFrobMap hA1
  let T : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lCD c d) :=
    LinearMap.codRestrict (KF 3 (lCD c d)) ((KF 3 (lP c d)).subtype ∘ₗ T1)
      (fun f => mem_lCD c d (T1 f) (hland f))
  have hT : IsRealIntertwinerModulo 3 (lDC c d) (lCD c d) ⊥ T :=
    modulo_bot_of_coe (modulo_comp_bot hA0m hA1m) (fun _ => rfl)
  -- `T` is injective by the uncertainty principle
  have hTi : Function.Injective T := by
    refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
    have h1 : blockFrobMap hA0 (blockFrobMap hA1 f) = 0 := by
      apply Subtype.ext
      have h0 := congrArg Subtype.val hf
      exact h0
    have h2 : blockFrobMap hA1 f = 0 := hA0i (by rw [map_zero]; exact h1)
    have hhigh := modes_of_tail_eq_zero hm0 hε hparT hσ hA1 f h2
    exact eq_zero_of_unitaryCompact f (hU 0 1 d.weight.natAbs m f (Or.inl ⟨rfl, rfl⟩) hml
      (continuous_coe f) f.2.2
      (fun g _ j hj => f.2.1.2 0 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hj) g)
      (fun g hg j hj => hhigh g hg j hj))
  have hTs : Function.Surjective T :=
    RealKTypeTransport.surjective_of_injective_induced_character c d hT.isRealKEquivariant hTi
  exact ⟨T, ⟨hTi, hTs⟩, hT⟩

/-- Tail-second bijection, from the character-first space to the induction-first space. -/
theorem exists_bijective_tail_second {m : ℕ} (hm0 : 0 < m)
    (hml : m < d.weight.natAbs) (hw : (chB d).exponent - c.exponent = -(m : ℂ))
    (hpar : (m + c.parity.val) % 2 = 0) :
    ∃ E : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d),
      Function.Bijective E ∧ IsRealIntertwinerModulo 3 (lCD c d) (lDC c d) ⊥ E := by
  have hLC := RealSwapLandingMirror.characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst
  have hU := RealOrthogonalUncertainty.realOrthogonalBlockUncertainty
  have hw' : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(m : ℂ) := hw
  have hε₀ := pairParity_eq c (chA d)
  have hl0 : 0 < d.weight.natAbs - m := Nat.sub_pos_of_lt hml
  have hparT : Even (((d.weight.natAbs - m : ℕ) : ℤ) - 1 - pairParity c (chA d)) := by
    rw [pairParity_c_chA, Int.even_iff]
    omega
  have hσ₀ : (sigma0 c (chA d)) ^ 2 = 1 := by
    rw [sigma0_eq, mul_pow, neg_one_pow_sq_fin, neg_one_pow_sq_fin, one_mul]
  -- the tail map `B₀` along `r₀`
  have hs₀ := isSymmetric_tailMultiplier hl0 hε₀ hparT hσ₀
  have hB0 := dataB0 c d hs₀
  have hrec₀ : IsRecurrent (1 - ((d.weight.natAbs - m : ℕ) : ℂ)) (pairParity c (chA d))
      (tailMultiplier (d.weight.natAbs - m) (pairParity c (chA d)) (sigma0 c (chA d))) :=
    isRecurrent_tailMultiplier hl0 hε₀ hparT hσ₀
  have hB0m : IsRealIntertwinerModulo 3 (lCD c d) (lM c d) ⊥ (blockFrobMap hB0) := by
    refine isRealIntertwinerModulo_blockFrobMap hB0 ?_ ⊥
    rw [posExp_lCD_0, posExp_lCD_1,
      show c.exponent - (d.exponent + (d.weight.natAbs : ℂ) / 2) + 1 =
          1 - ((d.weight.natAbs - m : ℕ) : ℂ) by
        rw [Nat.cast_sub hml.le]
        linear_combination -hw']
    exact hrec₀
  -- the generic swap `B₁` along `r₁`, with `ν₁ = s - b = m₀`
  have hε₁ := pairParity_eq (chB d) c
  have hν₁re : 0 < ((m : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast hm0
  have hs₁ := isSymmetric_genericMultiplier (m : ℂ) hε₁
  have hB1 := dataB1 c d hs₁
  have hrec₁ : IsRecurrent ((m : ℂ) + 1) (pairParity (chB d) c)
      (genericMultiplier (m : ℂ) (pairParity (chB d) c)) :=
    isRecurrent_genericMultiplier hν₁re hε₁
  have hB1m : IsRealIntertwinerModulo 3 (lM c d) (lQ c d) ⊥ (blockFrobMap hB1) := by
    refine isRealIntertwinerModulo_blockFrobMap hB1 ?_ ⊥
    rw [posExp_lM_1', posExp_lM_2,
      show c.exponent - (chB d).exponent + 1 = (m : ℂ) + 1 by linear_combination -hw]
    exact hrec₁
  have hB1i : Function.Injective (blockFrobMap hB1) :=
    frob_injective_of_ne_zero hB1 fun k _ => genericMultiplier_ne_zero hν₁re hε₁ (fun i h => by
      have e : (m : ℤ) = pairParity (chB d) c + 2 * i + 1 := by exact_mod_cast h
      rw [pairParity_chB_c] at e
      omega) k
  -- the composite lands in the standard module of `[d, c]`
  have hrec₁' : IsRecurrent (1 - ((d.weight.natAbs - m : ℕ) : ℂ) + (d.weight.natAbs : ℂ))
      (c.parity.val : ℤ) (genericMultiplier (m : ℂ) (pairParity (chB d) c)) := by
    rw [show 1 - ((d.weight.natAbs - m : ℕ) : ℂ) + (d.weight.natAbs : ℂ) = (m : ℂ) + 1 by
      rw [Nat.cast_sub hml.le]
      ring]
    exact isRecurrent_of_even hrec₁ (even_class_chB_c c d)
  have hland : ∀ f : KF 3 (lCD c d), ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 0 k
        ((blockFrobMap hB1 (blockFrobMap hB0 f) : KF 3 (lQ c d)) :
          Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := fun f =>
    hLC c d (1 - ((d.weight.natAbs - m : ℕ) : ℂ)) _ _ (f : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hB0 f : KF 3 (lM c d)) : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hB1 (blockFrobMap hB0 f) : KF 3 (lQ c d)) :
        Langlands.GeneralLinear 3 ℝ → ℂ)
      (isRecurrent_of_even hrec₀ (even_class_c_chA c d))
      (isSymmetric_of_even hs₀ (even_class_c_chA c d) (sign_class_c_chA c d))
      hrec₁' (isSymmetric_of_even hs₁ (even_class_chB_c c d) (sign_class_chB_c c d))
      f.2 (continuous_coe _) (continuous_coe _)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hB0 f hg k)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hB1 _ hg k)
  let E1 : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lQ c d) := blockFrobMap hB1 ∘ₗ blockFrobMap hB0
  let E : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d) :=
    LinearMap.codRestrict (KF 3 (lDC c d)) ((KF 3 (lQ c d)).subtype ∘ₗ E1)
      (fun f => mem_lDC c d (E1 f) (hland f))
  have hE : IsRealIntertwinerModulo 3 (lCD c d) (lDC c d) ⊥ E :=
    modulo_bot_of_coe (modulo_comp_bot hB1m hB0m) (fun _ => rfl)
  -- `E` is injective by the uncertainty principle
  have hEi : Function.Injective E := by
    refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
    have h1 : blockFrobMap hB1 (blockFrobMap hB0 f) = 0 := by
      apply Subtype.ext
      have h0 := congrArg Subtype.val hf
      exact h0
    have h2 : blockFrobMap hB0 f = 0 := hB1i (by rw [map_zero]; exact h1)
    have hhigh := modes_of_tail_eq_zero hl0 hε₀ hparT hσ₀ hB0 f h2
    exact eq_zero_of_unitaryCompact f (hU 1 0 d.weight.natAbs (d.weight.natAbs - m) f
      (Or.inr ⟨rfl, rfl⟩) (Nat.sub_lt (by omega) hm0) (continuous_coe f) f.2.2
      (fun g _ j hj => f.2.1.2 1 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hj) g)
      (fun g hg j hj => hhigh g hg j hj))
  have hEs : Function.Surjective E :=
    RealKTypeTransport.surjective_of_injective_character_induced c d hE.isRealKEquivariant hEi
  have hb : Function.Bijective E := ⟨hEi, hEs⟩
  exact ⟨E, hb, hE⟩


/-- There is a bijective exact intertwiner whenever `b - s = -m`, `0 < m < |weight|`. -/
theorem exists_bijective_interlaced {m : ℕ} (hm0 : 0 < m) (hml : m < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(m : ℂ)) :
    ∃ T : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d), Function.Bijective T ∧
      IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC c d))
        (realStandardLie 3 (lDC c d)) (lCD c d) T := by
  have hmod : ∃ T : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d), Function.Bijective T ∧
      IsRealIntertwinerModulo 3 (lCD c d) (lDC c d) ⊥ T := by
    rcases Nat.mod_two_eq_zero_or_one (m + c.parity.val) with hpar | hpar
    · exact exists_bijective_tail_second c d hm0 hml hw hpar
    · obtain ⟨T, hb, hT⟩ := exists_bijective_tail_first c d hm0 hml hw hpar
      exact ⟨(LinearEquiv.ofBijective T hb).symm.toLinearMap,
        (LinearEquiv.ofBijective T hb).symm.bijective, modulo_symm hT hb⟩
  obtain ⟨T, hb, hT⟩ := hmod
  refine ⟨T, hb, ?_⟩
  simpa only [LinearMap.id_comp] using
    hT.comp (isRealStandardIntertwiner_id 3 (lDC c d)) bot_le

/-- A chosen linear equivalence for an interlaced integral character-induced pair. -/
def interlacedEquiv {m : ℕ} (hm0 : 0 < m) (hml : m < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(m : ℂ)) :
    KF 3 (lCD c d) ≃ₗ[ℂ] KF 3 (lDC c d) :=
  LinearEquiv.ofBijective (Classical.choose (exists_bijective_interlaced c d hm0 hml hw))
    (Classical.choose_spec (exists_bijective_interlaced c d hm0 hml hw)).1

/-- The chosen equivalence commutes with the compact action and the real Lie derivatives. -/
theorem interlacedEquiv_isIntertwiner {m : ℕ} (hm0 : 0 < m) (hml : m < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(m : ℂ)) :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC c d))
      (realStandardLie 3 (lDC c d)) (lCD c d)
      (interlacedEquiv c d hm0 hml hw).toLinearMap :=
  (Classical.choose_spec (exists_bijective_interlaced c d hm0 hml hw)).2

/-- The interlaced integral case of the injective swap. -/
theorem injective_interlaced {m : ℕ} (hm0 : 0 < m) (hml : m < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(m : ℂ)) :
    RealInjectiveIntertwinerExists 3 (lCD c d) (lDC c d) :=
  ⟨(interlacedEquiv c d hm0 hml hw).toLinearMap,
    (interlacedEquiv c d hm0 hml hw).injective,
    interlacedEquiv_isIntertwiner c d hm0 hml hw⟩

end RealCharacterInducedInterlaced

end Langlands.Archimedean
