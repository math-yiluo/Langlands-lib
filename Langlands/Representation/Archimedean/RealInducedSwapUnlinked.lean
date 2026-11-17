import Langlands.Representation.Archimedean.RealInducedSwapScalarLimit
import Langlands.Representation.Archimedean.RealInducedSwapBalanced
import Langlands.Representation.Archimedean.RealInducedSwapIntegralReduction
import Langlands.Representation.Archimedean.RealInducedSwapIntegralNormalization

/-!
# The unlinked swap of two induction blocks
-/

noncomputable section

open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapUnlinked

open Langlands.LocalFactor.Archimedean
open RealCharacterInducedSwap RealInducedSwapGeneric RealInducedSwapInverse
open RealInducedSwapIntegralReduction RealInducedSwapBalanced RealInducedSwapLimit
open RealInducedSwapScalarLimit

/-- In the integral window the two central exponents have equal imaginary parts. -/
theorem im_eq_of_integralWindow {d e : ComplexCharacterData} {m : ℕ}
    (hw : IntegralWindow d e m) : d.exponent.im = e.exponent.im := by
  have h := congrArg Complex.im hw.2.2
  simp only [chA_exponent, chB_exponent, Complex.sub_im, Complex.add_im, Complex.div_im,
    Complex.natCast_re, Complex.natCast_im, Complex.neg_im] at h
  norm_num at h
  linarith

/-- Two balanced valid normalizations and equal imaginary parts give the swap. -/
theorem swap_of_balanced (d e : ComplexCharacterData) (a b : Normalization)
    (ha : IsValid d e a) (hb : IsValid e d b) (hab : Balanced a b)
    (him : d.exponent.im = e.exponent.im) :
    RealInjectiveIntertwinerExists 4 (source d e) (target d e) := by
  obtain ⟨L, hne, hL, hpath⟩ := hasGenericPath_of_im_eq d e him
  have := hne
  exact realInjectiveIntertwinerExists_of_weaklyAnalytic_smul d e hL (targetFamily d e a ha)
    (targetFamily_analytic d e a ha)
    (hpath.mono fun z hz => ⟨hz.1, scalar a z, genericFourCrossings hz.2,
      targetFamily_eq_generic d e a ha hz.1 hz.2⟩)
    (targetFamily_zero_injective d e a ha b hb hab hL hpath)

/-- Balanced valid normalizations in every integral window give `IntegralSwapStatement`. -/
theorem integralSwap_of_exists_balanced
    (h : ∀ d e : ComplexCharacterData, d.weight ≠ 0 → e.weight ≠ 0 →
      d.weight.natAbs ≠ e.weight.natAbs → ∀ m : ℕ, IntegralWindow d e m →
        ∃ a b : Normalization, IsValid d e a ∧ IsValid e d b ∧ Balanced a b) :
    IntegralSwapStatement := by
  intro d e hd he hne m hw
  obtain ⟨a, b, ha, hb, hab⟩ := h d e hd he hne m hw
  exact swap_of_balanced d e a b ha hb hab (im_eq_of_integralWindow hw)

end RealInducedSwapUnlinked

/-- The `GL_4` unlinked swap of two real induction blocks of nonzero weights. -/
theorem realInducedSwap : RealInducedSwapStatement :=
  RealInducedSwapIntegralReduction.realInducedSwap_iff_integral.mpr
    (RealInducedSwapUnlinked.integralSwap_of_exists_balanced
      fun _ _ hd he hne m hw =>
        RealInducedSwapIntegralNormalization.exists_balanced_of_integralWindow hd he hne m hw)

end Langlands.Archimedean
