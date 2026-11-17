import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability

noncomputable section

universe u v w

namespace Langlands.Analytic

open scoped TensorProduct
open TensorProduct

/-- Flatness over a base descends through a faithfully flat extension of
the target algebra. -/
theorem flat_of_faithfullyFlat_target
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let fS := AlgebraTensorModule.lTensor S S f
  change Function.Injective fS
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T fS).mp
  apply Function.Injective.of_comp
    (f := AlgebraTensorModule.cancelBaseChange R S S T P)
  change Function.Injective
    ((AlgebraTensorModule.cancelBaseChange R S S T P).toLinearMap.comp
      (AlgebraTensorModule.lTensor S T fS))
  rw [← AlgebraTensorModule.lTensor_comp_cancelBaseChange]
  exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp
      (AlgebraTensorModule.cancelBaseChange R S S T N).injective

end Langlands.Analytic
