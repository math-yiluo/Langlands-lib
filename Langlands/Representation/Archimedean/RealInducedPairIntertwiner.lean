import Langlands.Representation.Archimedean.RealInducedPairFrobenius
import Langlands.Representation.Archimedean.RealStandardFiltration

/-!
# Intertwining of the four-crossing induced-pair map

The recurrence parameters of the four crossings are the differences of their
actual position exponents, plus one.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairFrobenius

open RealBlockFrobeniusMap RealBlockMultiplier RealStandardFiltration

set_option backward.isDefEq.respectTransparency false

/-- The exponent difference plus one at the first crossing. -/
def swapParameter (d e : ComplexCharacterData) : ℂ :=
  d.exponent - (d.weight.natAbs : ℂ) / 2 -
    e.exponent - (e.weight.natAbs : ℂ) / 2 + 1

private theorem inclusion_intertwiner (d e : ComplexCharacterData) :
    IsRealIntertwinerModulo 4 (src d e) (l0 d e) ⊥
      (Submodule.inclusion (src_le_l0 d e)) := by
  refine ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule
      4 (src d e) f.2 k.2, ?_, ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule
      4 (src d e) f.2 X, ?_, ?_⟩⟩
  · exact src_le_l0 d e
      (rightTranslation_mem_kFiniteFunctions_realStandardModule 4 (src d e) f.2 k.2)
  · rw [Submodule.mem_bot, sub_eq_zero]
    rfl
  · exact src_le_l0 d e
      (rightDerivative_mem_kFiniteFunctions_realStandardModule 4 (src d e) f.2 X)
  · rw [Submodule.mem_bot, sub_eq_zero]
    rfl

namespace MultiplierData

variable {d e : ComplexCharacterData} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
    (h : MultiplierData d e (swapParameter d e) μ₁ μ₀ μ₂ μ₃)

include h

/-- Each of the four maps intertwines at its actual exponent difference. -/
theorem to4_isRealIntertwinerModulo :
    IsRealIntertwinerModulo 4 (src d e) (l4 d e) ⊥ h.to4 := by
  have h1 : IsRealIntertwinerModulo 4 (l0 d e) (l1 d e) ⊥
      (blockFrobMap h.data1) := by
    refine isRealIntertwinerModulo_blockFrobMap h.data1 ?_ ⊥
    convert h.rec1 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
        RealJacquetFrobenius.charData, swapParameter]
    ring
  have h0 : IsRealIntertwinerModulo 4 (l1 d e) (l10 d e) ⊥
      (blockFrobMap h.data0) := by
    refine isRealIntertwinerModulo_blockFrobMap h.data0 ?_ ⊥
    convert h.rec0 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
        RealJacquetFrobenius.charData, swapParameter]
    ring
  have h2 : IsRealIntertwinerModulo 4 (l10 d e) (l3 d e) ⊥
      (blockFrobMap h.data20) := by
    refine isRealIntertwinerModulo_blockFrobMap h.data20 ?_ ⊥
    convert h.rec2 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
        RealJacquetFrobenius.charData, swapParameter]
    ring
  have h3 : IsRealIntertwinerModulo 4 (l3 d e) (l4 d e) ⊥
      (blockFrobMap h.data3) := by
    refine isRealIntertwinerModulo_blockFrobMap h.data3 ?_ ⊥
    convert h.rec3 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
        RealJacquetFrobenius.charData, swapParameter]
    ring
  exact modulo_comp_bot h3
    (modulo_comp_bot h2 (modulo_comp_bot h0
      (modulo_comp_bot h1 (inclusion_intertwiner d e))))

/-- Codomain restriction preserves the exact intertwining identities. -/
theorem swap_isRealIntertwinerModulo
    (M : Submodule ℂ (KF (dst d e))) :
    IsRealIntertwinerModulo 4 (src d e) (dst d e) M h.swap := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, hzero⟩ := h.to4_isRealIntertwinerModulo.1 k f
    refine ⟨hf, rightTranslation_mem_kFiniteFunctions_realStandardModule
      4 (dst d e) (h.swap f).2 k.2, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at hzero
    have heq : h.swap ⟨_, hf⟩ =
        ⟨_, rightTranslation_mem_kFiniteFunctions_realStandardModule
          4 (dst d e) (h.swap f).2 k.2⟩ := by
      apply Subtype.ext
      exact congrArg (fun z : KF (l4 d e) =>
        (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hzero
    rw [heq, sub_self]
    exact M.zero_mem
  · obtain ⟨hf, hg, hzero⟩ := h.to4_isRealIntertwinerModulo.2 X f
    refine ⟨hf, rightDerivative_mem_kFiniteFunctions_realStandardModule
      4 (dst d e) (h.swap f).2 X, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at hzero
    have heq : h.swap ⟨_, hf⟩ =
        ⟨_, rightDerivative_mem_kFiniteFunctions_realStandardModule
          4 (dst d e) (h.swap f).2 X⟩ := by
      apply Subtype.ext
      exact congrArg (fun z : KF (l4 d e) =>
        (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hzero
    rw [heq, sub_self]
    exact M.zero_mem

end MultiplierData

end RealInducedPairFrobenius

/-- The four-crossing exchange map intertwines for the prescribed exponent parameter. -/
def RealInducedPairIntertwinerStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ)
    (h : RealInducedPairFrobenius.MultiplierData d e
      (RealInducedPairFrobenius.swapParameter d e) μ₁ μ₀ μ₂ μ₃),
    IsRealIntertwinerModulo 4
      (RealInducedPairFrobenius.src d e) (RealInducedPairFrobenius.dst d e) ⊥ h.swap

theorem realInducedPairIntertwiner : RealInducedPairIntertwinerStatement := by
  intro d e μ₁ μ₀ μ₂ μ₃ h
  exact h.swap_isRealIntertwinerModulo ⊥

end Langlands.Archimedean
