import Langlands.Representation.Archimedean.RealCharacterInducedSwap
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror
import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric
import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-!
# Character-induced swaps with two generic factors

The two block Frobenius maps in the character-first direction are injective when
both parameters avoid their rank-one exceptional sets. Their composite lands in
the induction-first standard module by the proved landing theorem.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealCharacterInducedGeneric

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap RealCharacterInducedPushforward
open Langlands.LocalFactor.Archimedean

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- If both character-first Frobenius parameters are generic, their composite is an
injective exact intertwiner between the actual mixed standard modules. -/
theorem injective_of_generic
    (h0 : IsGenericParameter (c.exponent - (chA d).exponent) (pairParity c (chA d)))
    (h1 : IsGenericParameter (c.exponent - (chB d).exponent) (pairParity (chB d) c)) :
    RealInjectiveIntertwinerExists 3 (lCD c d) (lDC c d) := by
  let ν0 := c.exponent - (chA d).exponent
  let ν1 := c.exponent - (chB d).exponent
  have hε0 := pairParity_eq c (chA d)
  have hε1 := pairParity_eq (chB d) c
  have hs0 := isSymmetric_genericMultiplier ν0 hε0
  have hs1 := isSymmetric_genericMultiplier ν1 hε1
  have hB0 := dataB0 c d hs0
  have hB1 := dataB1 c d hs1
  have hrec0 := isRecurrent_genericMultiplier_of_ne hε0 h0.2
  have hrec1 := isRecurrent_genericMultiplier_of_ne hε1 h1.2
  have hB0m : IsRealIntertwinerModulo 3 (lCD c d) (lM c d) ⊥ (blockFrobMap hB0) := by
    refine isRealIntertwinerModulo_blockFrobMap hB0 ?_ ⊥
    rw [posExp_lCD_0, posExp_lCD_1]
    exact hrec0
  have hB1m : IsRealIntertwinerModulo 3 (lM c d) (lQ c d) ⊥ (blockFrobMap hB1) := by
    refine isRealIntertwinerModulo_blockFrobMap hB1 ?_ ⊥
    rw [posExp_lM_1', posExp_lM_2]
    exact hrec1
  have hB0i : Function.Injective (blockFrobMap hB0) :=
    frob_injective_of_ne_zero hB0 fun k _ => genericMultiplier_ne_zero_of_ne h0.1 h0.2 k
  have hB1i : Function.Injective (blockFrobMap hB1) :=
    frob_injective_of_ne_zero hB1 fun k _ => genericMultiplier_ne_zero_of_ne h1.1 h1.2 k
  have hparam : ν0 + 1 + (d.weight.natAbs : ℂ) = ν1 + 1 := by
    dsimp [ν0, ν1]
    rw [chA_exponent, chB_exponent]
    ring
  have hrec1' : IsRecurrent (ν0 + 1 + (d.weight.natAbs : ℂ)) (c.parity.val : ℤ)
      (genericMultiplier ν1 (pairParity (chB d) c)) := by
    rw [hparam]
    exact isRecurrent_of_even hrec1 (even_class_chB_c c d)
  have hLC := RealSwapLandingMirror.characterFirst_of_inducedFirst
    RealSwapLandingIntegral.inducedFirst
  have hland : ∀ f : KF 3 (lCD c d), ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 0 k
        ((blockFrobMap hB1 (blockFrobMap hB0 f) : KF 3 (lQ c d)) :
          Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := fun f =>
    hLC c d (ν0 + 1) _ _ (f : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hB0 f : KF 3 (lM c d)) : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hB1 (blockFrobMap hB0 f) : KF 3 (lQ c d)) :
        Langlands.GeneralLinear 3 ℝ → ℂ)
      (isRecurrent_of_even hrec0 (even_class_c_chA c d))
      (isSymmetric_of_even hs0 (even_class_c_chA c d) (sign_class_c_chA c d))
      hrec1' (isSymmetric_of_even hs1 (even_class_chB_c c d) (sign_class_chB_c c d))
      f.2 (continuous_coe _) (continuous_coe _)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hB0 f hg k)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hB1 _ hg k)
  let E1 : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lQ c d) := blockFrobMap hB1 ∘ₗ blockFrobMap hB0
  let E : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d) :=
    LinearMap.codRestrict (KF 3 (lDC c d)) ((KF 3 (lQ c d)).subtype ∘ₗ E1)
      (fun f => mem_lDC c d (E1 f) (hland f))
  have hE : IsRealIntertwinerModulo 3 (lCD c d) (lDC c d) ⊥ E :=
    modulo_bot_of_coe (modulo_comp_bot hB1m hB0m) (fun _ => rfl)
  have hEi : Function.Injective E := by
    intro f g hfg
    apply hB0i
    apply hB1i
    apply Subtype.ext
    have h := congrArg (fun v : KF 3 (lDC c d) =>
      (v : Langlands.GeneralLinear 3 ℝ → ℂ)) hfg
    exact h
  refine ⟨E, hEi, ?_⟩
  simpa only [LinearMap.id_comp] using
    hE.comp (isRealStandardIntertwiner_id 3 (lDC c d)) bot_le

/-- A chosen generic composite between the two mixed standard modules. -/
def genericMap
    (h0 : IsGenericParameter (c.exponent - (chA d).exponent) (pairParity c (chA d)))
    (h1 : IsGenericParameter (c.exponent - (chB d).exponent) (pairParity (chB d) c)) :
    KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d) :=
  Classical.choose (injective_of_generic c d h0 h1)

theorem genericMap_injective
    (h0 : IsGenericParameter (c.exponent - (chA d).exponent) (pairParity c (chA d)))
    (h1 : IsGenericParameter (c.exponent - (chB d).exponent) (pairParity (chB d) c)) :
    Function.Injective (genericMap c d h0 h1) :=
  (Classical.choose_spec (injective_of_generic c d h0 h1)).1

theorem genericMap_isIntertwiner
    (h0 : IsGenericParameter (c.exponent - (chA d).exponent) (pairParity c (chA d)))
    (h1 : IsGenericParameter (c.exponent - (chB d).exponent) (pairParity (chB d) c)) :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC c d))
      (realStandardLie 3 (lDC c d)) (lCD c d) (genericMap c d h0 h1) :=
  (Classical.choose_spec (injective_of_generic c d h0 h1)).2

end RealCharacterInducedGeneric

end Langlands.Archimedean
