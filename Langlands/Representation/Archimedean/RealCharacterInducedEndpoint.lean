import Langlands.Representation.Archimedean.RealCharacterInducedInterlaced
import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric

/-!
# The odd endpoint of the character-induced swap

Extends the tail-first construction to b-s=-|weight|. The zero generic parameter
is harmless, and parity strengthens the induction block's low-mode vanishing.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

namespace RealCharacterInducedEndpoint

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap RealCharacterInducedPushforward
open Langlands.LocalFactor.Archimedean

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- An induction block has no Fourier modes strictly below `|weight|+1`. -/
theorem induced_first_low_modes (f : KF 3 (lDC c d)) (j : ℤ)
    (hj : |j| < ((d.weight.natAbs + 1 : ℕ) : ℤ)) (g : Langlands.GeneralLinear 3 ℝ) :
    blockFourierCoefficient 3 0 j (f : Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := by
  by_cases hlow : |j| < (d.weight.natAbs : ℤ)
  · exact f.2.1.2 0 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hlow) g
  · have hpar : (-1 : ℂ) ^ (((d.weight.natAbs + 1) % 2 : ℕ) : ℤ) =
        realPositionCharacter (lDC c d) 0 (-1) * realPositionCharacter (lDC c d) (0 + 1) (-1) := by
      rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one]
      change (-1 : ℂ) ^ (((d.weight.natAbs + 1) % 2 : ℕ) : ℤ) =
        (-1 : ℂ) ^ ((d.weight.natAbs + 1) % 2) * (-1 : ℂ) ^ (0 : ℕ)
      simp only [zpow_natCast, pow_zero, mul_one]
    refine blockFourierCoefficient_eq_zero_of_not_even (by decide) hpar f ?_ g
    rw [Int.even_iff]
    have he : |j| = (d.weight.natAbs : ℤ) := by omega
    by_cases hjnonneg : 0 ≤ j
    · rw [abs_of_nonneg hjnonneg] at he
      omega
    · rw [abs_of_neg (by omega)] at he
      omega

/-- The tail-first map remains bijective at the odd endpoint. -/
theorem exists_bijective_tail_first (hl0 : 0 < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(d.weight.natAbs : ℂ))
    (hpar : (d.weight.natAbs + c.parity.val) % 2 = 1) :
    ∃ T : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lCD c d),
      Function.Bijective T ∧ IsRealIntertwinerModulo 3 (lDC c d) (lCD c d) ⊥ T := by
  have hLI := RealSwapLandingIntegral.inducedFirst
  have hU := RealOrthogonalUncertainty.realOrthogonalBlockUncertainty
  have hw' : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(d.weight.natAbs : ℂ) := hw
  have hε := parity_cases c
  have hparT : Even ((d.weight.natAbs : ℤ) - 1 - (c.parity.val : ℤ)) := by
    rw [Int.even_iff]
    omega
  have hσ : ((-1 : ℂ) ^ c.parity.val) ^ 2 = 1 := neg_one_pow_sq_fin c.parity
  -- the tail map `A₁` along `r₁`
  have hs₁ := isSymmetric_tailMultiplier hl0 hε hparT hσ
  have hA1 := dataA1 c d rfl hs₁
  have hrec₁ : IsRecurrent (1 - (d.weight.natAbs : ℂ)) (c.parity.val : ℤ)
      (tailMultiplier d.weight.natAbs (c.parity.val : ℤ) ((-1) ^ c.parity.val)) :=
    isRecurrent_tailMultiplier hl0 hε hparT hσ
  have hA1m : IsRealIntertwinerModulo 3 (lDC c d) (lM c d) ⊥ (blockFrobMap hA1) := by
    refine isRealIntertwinerModulo_blockFrobMap hA1 ?_ ⊥
    rw [posExp_lDC_1, posExp_lDC_2,
      show d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent + 1 = 1 - (d.weight.natAbs : ℂ) by
        linear_combination hw']
    exact hrec₁
  -- The zero-parameter generic swap has neither numerator nor denominator zeros.
  have hν₀ : (chA d).exponent - c.exponent = 0 := by
    rw [chA_exponent]
    linear_combination hw'
  have hε₀ := pairParity_eq c (chA d)
  have hε₀nonneg : 0 ≤ pairParity c (chA d) := by rcases hε₀ with h | h <;> omega
  have hden : ∀ i : ℕ, (0 : ℂ) ≠ -((pairParity c (chA d) : ℂ) + 2 * i + 1) :=
    ne_neg_of_re_nonneg (by simp) hε₀nonneg
  have hne : ∀ i : ℕ, (0 : ℂ) ≠ (pairParity c (chA d) : ℂ) + 2 * i + 1 := by
    intro i h
    have h' := congrArg Neg.neg h
    exact hden i (by simpa using h')
  have hs₀ := isSymmetric_genericMultiplier (0 : ℂ) hε₀
  have hA0 := dataA0 c d hs₀
  have hrec₀ : IsRecurrent ((0 : ℂ) + 1) (pairParity c (chA d))
      (genericMultiplier 0 (pairParity c (chA d))) :=
    isRecurrent_genericMultiplier_of_ne hε₀ hden
  have hA0m : IsRealIntertwinerModulo 3 (lM c d) (lP c d) ⊥ (blockFrobMap hA0) := by
    refine isRealIntertwinerModulo_blockFrobMap hA0 ?_ ⊥
    rw [posExp_lM_0, posExp_lM_1, hν₀]
    exact hrec₀
  have hA0i : Function.Injective (blockFrobMap hA0) :=
    frob_injective_of_ne_zero hA0 fun k _ => genericMultiplier_ne_zero_of_ne hne hden k
  -- the composite lands in the standard module of `[c, d]`
  have hrec₀' : IsRecurrent (1 - (d.weight.natAbs : ℂ) + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      (genericMultiplier 0 (pairParity c (chA d))) := by
    rw [show 1 - (d.weight.natAbs : ℂ) + (d.weight.natAbs : ℂ) = 0 + 1 by ring]
    exact isRecurrent_of_even hrec₀ (even_class_c_chA c d)
  have hland : ∀ f : KF 3 (lDC c d), ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 1 k
        ((blockFrobMap hA0 (blockFrobMap hA1 f) : KF 3 (lP c d)) :
          Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := fun f =>
    hLI c d (1 - (d.weight.natAbs : ℂ)) _ _ (f : Langlands.GeneralLinear 3 ℝ → ℂ)
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
    have hhigh := modes_of_tail_eq_zero hl0 hε hparT hσ hA1 f h2
    exact eq_zero_of_unitaryCompact f (hU 0 1 (d.weight.natAbs + 1) d.weight.natAbs f
      (Or.inl ⟨rfl, rfl⟩) (Nat.lt_succ_self _) (continuous_coe f) f.2.2
      (fun g _ j hj => induced_first_low_modes c d f j hj g)
      (fun g hg j hj => hhigh g hg j hj))
  have hTs : Function.Surjective T :=
    RealKTypeTransport.surjective_of_injective_induced_character c d hT.isRealKEquivariant hTi
  exact ⟨T, ⟨hTi, hTs⟩, hT⟩

/-- A forward bijective exact intertwiner at the odd endpoint. -/
theorem exists_bijective_endpoint (hl0 : 0 < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(d.weight.natAbs : ℂ))
    (hpar : (d.weight.natAbs + c.parity.val) % 2 = 1) :
    ∃ T : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d), Function.Bijective T ∧
      IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC c d))
        (realStandardLie 3 (lDC c d)) (lCD c d) T := by
  obtain ⟨T, hb, hT⟩ := exists_bijective_tail_first c d hl0 hw hpar
  have hmod := modulo_symm hT hb
  refine ⟨(LinearEquiv.ofBijective T hb).symm.toLinearMap,
    (LinearEquiv.ofBijective T hb).symm.bijective, ?_⟩
  simpa only [LinearMap.id_comp] using
    hmod.comp (isRealStandardIntertwiner_id 3 (lDC c d)) bot_le

/-- A chosen equivalence for the odd endpoint character-induced pair. -/
def endpointEquiv (hl0 : 0 < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(d.weight.natAbs : ℂ))
    (hpar : (d.weight.natAbs + c.parity.val) % 2 = 1) :
    KF 3 (lCD c d) ≃ₗ[ℂ] KF 3 (lDC c d) :=
  LinearEquiv.ofBijective (Classical.choose (exists_bijective_endpoint c d hl0 hw hpar))
    (Classical.choose_spec (exists_bijective_endpoint c d hl0 hw hpar)).1

/-- The endpoint equivalence commutes with the compact and real Lie actions. -/
theorem endpointEquiv_isIntertwiner (hl0 : 0 < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(d.weight.natAbs : ℂ))
    (hpar : (d.weight.natAbs + c.parity.val) % 2 = 1) :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC c d))
      (realStandardLie 3 (lDC c d)) (lCD c d)
      (endpointEquiv c d hl0 hw hpar).toLinearMap :=
  (Classical.choose_spec (exists_bijective_endpoint c d hl0 hw hpar)).2

/-- The odd endpoint case of the injective character-induced swap. -/
theorem injective_endpoint (hl0 : 0 < d.weight.natAbs)
    (hw : (chB d).exponent - c.exponent = -(d.weight.natAbs : ℂ))
    (hpar : (d.weight.natAbs + c.parity.val) % 2 = 1) :
    RealInjectiveIntertwinerExists 3 (lCD c d) (lDC c d) :=
  ⟨(endpointEquiv c d hl0 hw hpar).toLinearMap,
    (endpointEquiv c d hl0 hw hpar).injective,
    endpointEquiv_isIntertwiner c d hl0 hw hpar⟩

end RealCharacterInducedEndpoint

end Langlands.Archimedean
